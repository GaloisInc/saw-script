{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Simulator.SBV.Value
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}
module Verifier.SAW.Simulator.SBV.Value where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Traversable
#endif
import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Verifier.SAW.Recognizer as R
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

-- | First-order types that can be encoded in a SAT/SMT solver.
data FiniteType
  = FTBit
  | FTInteger
  | FTVec Nat FiniteType
  | FTTuple [FiniteType]
  | FTRec (Map FieldName FiniteType)
  deriving (Eq, Show)

-- | Values inhabiting those first-order types.
data FiniteValue
  = FVBit Bool
  | FVInteger Integer
  | FVWord Nat Integer -- ^ a more efficient special case for 'FVVec FTBit _'.
  | FVVec FiniteType [FiniteValue]
  | FVTuple [FiniteValue]
  | FVRec (Map FieldName FiniteValue)
  deriving Eq

instance Show FiniteValue where
  showsPrec _ fv =
    case fv of
      FVBit b     -> shows b
      FVInteger i -> shows i
      FVWord _ x  -> shows x
      FVVec _ vs  -> showString "[" . commaSep (map shows vs) . showString "]"
      FVTuple vs  -> showString "(" . commaSep (map shows vs) . showString ")"
      FVRec vm    -> showString "{" . commaSep (map showField (Map.assocs vm)) . showString "}"
    where
      commaSep ss = foldr (.) id (intersperse (showString ",") ss)
      showField (field, v) = showString field . showString " = " . shows v

-- | Smart constructor
fvVec :: FiniteType -> [FiniteValue] -> FiniteValue
fvVec t vs =
  case (t, traverse toBit vs) of
    (FTBit, Just bs) -> FVWord (fromIntegral (length bs)) (fromBits bs)
    _ -> FVVec t vs
  where
    toBit :: FiniteValue -> Maybe Bool
    toBit (FVBit b) = Just b
    toBit _ = Nothing

    fromBits :: [Bool] -> Integer
    fromBits = foldl (\n b -> 2*n + if b then 1 else 0) 0

finiteTypeOf :: FiniteValue -> FiniteType
finiteTypeOf fv =
  case fv of
    FVBit _     -> FTBit
    FVInteger _ -> FTInteger
    FVWord n _  -> FTVec n FTBit
    FVVec t vs  -> FTVec (fromIntegral (length vs)) t
    FVTuple vs  -> FTTuple (map finiteTypeOf vs)
    FVRec vm    -> FTRec (fmap finiteTypeOf vm)

asFiniteType :: SharedContext -> Term -> IO FiniteType
asFiniteType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asBoolType -> Just ())
      -> return FTBit
    (R.asIntegerType -> Just ())
      -> return FTInteger
    (R.isVecType return -> Just (n R.:*: tp))
      -> FTVec n <$> asFiniteType sc tp
    (R.asTupleType -> Just ts)
      -> FTTuple <$> traverse (asFiniteType sc) ts
    (R.asRecordType -> Just tm)
      -> FTRec <$> traverse (asFiniteType sc) tm
    _ -> fail $ "asFiniteType: unsupported argument type: " ++ show t'

-- | Convert a finite type to a Term.
scFiniteType :: SharedContext -> FiniteType -> IO Term
scFiniteType sc ft =
  case ft of
    FTBit      -> scBoolType sc
    FTInteger  -> scIntegerType sc
    FTVec n t  -> do n' <- scNat sc n
                     t' <- scFiniteType sc t
                     scVecType sc n' t'
    FTTuple ts -> scTupleType sc =<< traverse (scFiniteType sc) ts
    FTRec tm   -> scRecordType sc =<< traverse (scFiniteType sc) tm

-- | Convert a finite value to a SharedTerm.
scFiniteValue :: SharedContext -> FiniteValue -> IO Term
scFiniteValue sc fv =
  case fv of
    FVBit b    -> scBool sc b
    FVInteger i
      | i >= 0 -> scNatToInt sc =<< scNat sc (fromInteger i)
      | True   -> scIntNeg sc =<< scNatToInt sc =<< scNat sc (fromInteger (- i))
    FVWord n x -> scBvConst sc n x
    FVVec t vs -> do t' <- scFiniteType sc t
                     vs' <- traverse (scFiniteValue sc) vs
                     scVector sc t' vs'
    FVTuple vs -> scTuple sc =<< traverse (scFiniteValue sc) vs
    FVRec vm   -> scRecord sc =<< traverse (scFiniteValue sc) vm
