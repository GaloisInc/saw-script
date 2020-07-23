{-# LANGUAGE CPP #-}

{- |
Module      : Verifier.SAW.FiniteValue
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}
module Verifier.SAW.FiniteValue where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Traversable
#endif
import qualified Control.Monad.State as S
import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Numeric.Natural (Natural)

import qualified Verifier.SAW.Recognizer as R
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.Term.Pretty

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

-- | Finite types that can be encoded as bits for a SAT/SMT solver.
data FiniteType
  = FTBit
  | FTVec Natural FiniteType
  | FTTuple [FiniteType]
  | FTRec (Map FieldName FiniteType)
  deriving (Eq, Show)

-- | Values inhabiting those finite types.
data FiniteValue
  = FVBit Bool
  | FVWord Natural Integer -- ^ a more efficient special case for 'FVVec FTBit _'.
  | FVVec FiniteType [FiniteValue]
  | FVTuple [FiniteValue]
  | FVRec (Map FieldName FiniteValue)
  deriving Eq

-- | First-order types that can be encoded in an SMT solver.
data FirstOrderType
  = FOTBit
  | FOTInt
  | FOTVec Natural FirstOrderType
  | FOTArray FirstOrderType FirstOrderType
  | FOTTuple [FirstOrderType]
  | FOTRec (Map FieldName FirstOrderType)
  deriving (Eq, Show)

-- | Values inhabiting those first-order types.
data FirstOrderValue
  = FOVBit Bool
  | FOVInt Integer
  | FOVWord Natural Integer -- ^ a more efficient special case for 'FOVVec FOTBit _'.
  | FOVVec FirstOrderType [FirstOrderValue]
  | FOVArray FirstOrderType FirstOrderType
  | FOVTuple [FirstOrderValue]
  | FOVRec (Map FieldName FirstOrderValue)
  deriving Eq

toFirstOrderType :: FiniteType -> FirstOrderType
toFirstOrderType ft =
  case ft of
    FTBit      -> FOTBit
    FTVec n t  -> FOTVec n (toFirstOrderType t)
    FTTuple ts -> FOTTuple (map toFirstOrderType ts)
    FTRec tm   -> FOTRec (fmap toFirstOrderType tm)

toFirstOrderValue :: FiniteValue -> FirstOrderValue
toFirstOrderValue fv =
  case fv of
    FVBit b    -> FOVBit b
    FVWord w i -> FOVWord w i
    FVVec t vs -> FOVVec (toFirstOrderType t) (map toFirstOrderValue vs)
    FVTuple vs -> FOVTuple (map toFirstOrderValue vs)
    FVRec vm   -> FOVRec (fmap toFirstOrderValue vm)

instance Show FiniteValue where
  showsPrec p fv = showsPrec p (toFirstOrderValue fv)

instance Show FirstOrderValue where
  showsPrec _ fv =
    case fv of
      FOVBit b    -> shows b
      FOVInt i    -> shows i
      FOVWord _ x -> shows x
      FOVVec _ vs -> showString "[" . commaSep (map shows vs) . showString "]"
      FOVArray{}  -> shows $ firstOrderTypeOf fv
      FOVTuple vs -> showString "(" . commaSep (map shows vs) . showString ")"
      FOVRec vm   -> showString "{" . commaSep (map showField (Map.assocs vm)) . showString "}"
    where
      commaSep ss = foldr (.) id (intersperse (showString ",") ss)
      showField (field, v) = showString field . showString " = " . shows v

ppFiniteValue :: PPOpts -> FiniteValue -> Doc
ppFiniteValue opts fv = ppFirstOrderValue opts (toFirstOrderValue fv)

ppFirstOrderValue :: PPOpts -> FirstOrderValue -> Doc
ppFirstOrderValue opts = loop
 where
 loop fv = case fv of
   FOVBit b
     | b         -> text "True"
     | otherwise -> text "False"
   FOVInt i      -> integer i
   FOVWord _w i  -> ppNat opts i
   FOVVec _ xs   -> brackets (sep (punctuate comma (map loop xs)))
   FOVArray{}    -> text $ show $ firstOrderTypeOf fv
   FOVTuple xs   -> parens (sep (punctuate comma (map loop xs)))
   FOVRec xs     -> braces (sep (punctuate comma (map ppField (Map.toList xs))))
      where ppField (f,x) = pretty f <+> char '=' <+> loop x


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

-- | Smart constructor
fovVec :: FirstOrderType -> [FirstOrderValue] -> FirstOrderValue
fovVec t vs =
  case (t, traverse toBit vs) of
    (FOTBit, Just bs) -> FOVWord (fromIntegral (length bs)) (fromBits bs)
    _ -> FOVVec t vs
  where
    toBit :: FirstOrderValue -> Maybe Bool
    toBit (FOVBit b) = Just b
    toBit _ = Nothing

    fromBits :: [Bool] -> Integer
    fromBits = foldl (\n b -> 2*n + if b then 1 else 0) 0

finiteTypeOf :: FiniteValue -> FiniteType
finiteTypeOf fv =
  case fv of
    FVBit _    -> FTBit
    FVWord n _ -> FTVec n FTBit
    FVVec t vs -> FTVec (fromIntegral (length vs)) t
    FVTuple vs -> FTTuple (map finiteTypeOf vs)
    FVRec vm   -> FTRec (fmap finiteTypeOf vm)

firstOrderTypeOf :: FirstOrderValue -> FirstOrderType
firstOrderTypeOf fv =
  case fv of
    FOVBit _    -> FOTBit
    FOVInt _    -> FOTInt
    FOVWord n _ -> FOTVec n FOTBit
    FOVVec t vs -> FOTVec (fromIntegral (length vs)) t
    -- Note: FOVArray contains type information, but not an actual Array value,
    -- because it is not possible to obtain Array values from SMT solvers. This
    -- is needed to display a counterexample that includes variables of Array
    -- type.
    FOVArray t1 t2 -> FOTArray t1 t2
    FOVTuple vs -> FOTTuple (map firstOrderTypeOf vs)
    FOVRec vm   -> FOTRec (fmap firstOrderTypeOf vm)

-- | Compute the number of bits in the type
sizeFiniteType :: FiniteType -> Int
sizeFiniteType x =
  case x of
    FTBit      -> 1
    FTVec n xs -> fromIntegral n * sizeFiniteType xs
    FTTuple xs -> sum (map sizeFiniteType xs)
    FTRec xm   -> sum (map sizeFiniteType (Map.elems xm))

asFiniteType :: SharedContext -> Term -> IO FiniteType
asFiniteType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asBoolType -> Just ())
      -> return FTBit
    (R.isVecType return -> Just (n R.:*: tp))
      -> FTVec n <$> asFiniteType sc tp
    (R.asTupleType -> Just ts)
      -> FTTuple <$> traverse (asFiniteType sc) ts
    (R.asRecordType -> Just tm)
      -> FTRec <$> traverse (asFiniteType sc) tm
    _ -> fail $ "asFiniteType: unsupported argument type: " ++ scPrettyTerm defaultPPOpts t'

asFirstOrderType :: SharedContext -> Term -> IO FirstOrderType
asFirstOrderType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asBoolType -> Just ())
      -> return FOTBit
    (R.asIntegerType -> Just ())
      -> return FOTInt
    (R.isVecType return -> Just (n R.:*: tp))
      -> FOTVec n <$> asFirstOrderType sc tp
    (R.asArrayType -> Just (tp1 R.:*: tp2)) -> do
      tp1' <- asFirstOrderType sc tp1
      tp2' <- asFirstOrderType sc tp2
      return $ FOTArray tp1' tp2'
    (R.asTupleType -> Just ts)
      -> FOTTuple <$> traverse (asFirstOrderType sc) ts
    (R.asRecordType -> Just tm)
      -> FOTRec <$> traverse (asFirstOrderType sc) tm
    _ -> fail $ "asFirstOrderType: unsupported argument type: " ++ scPrettyTerm defaultPPOpts t'

asFiniteTypePure :: Term -> Maybe FiniteType
asFiniteTypePure t =
  case t of
    (R.asBoolType -> Just ()) -> Just FTBit
    (R.isVecType return -> Just (n R.:*: tp)) -> FTVec n <$> asFiniteTypePure tp
    (R.asTupleType -> Just ts) -> FTTuple <$> traverse asFiniteTypePure ts
    (R.asRecordType -> Just tm) -> FTRec <$> traverse asFiniteTypePure tm
    _ -> Nothing

-- The definitions of the next two functions depend on the encoding of
-- tuples that we want to use. Maybe it is better not to include them
-- in this library, and we should have them in the SAWScript project
-- instead.

-- | Convert a finite type to a Term.
scFiniteType :: SharedContext -> FiniteType -> IO Term
scFiniteType sc ft = scFirstOrderType sc (toFirstOrderType ft)

-- | Convert a finite type to a Term.
scFirstOrderType :: SharedContext -> FirstOrderType -> IO Term
scFirstOrderType sc ft =
  case ft of
    FOTBit      -> scBoolType sc
    FOTInt      -> scIntegerType sc
    FOTVec n t  -> do n' <- scNat sc n
                      t' <- scFirstOrderType sc t
                      scVecType sc n' t'
    FOTArray t1 t2 -> do t1' <- scFirstOrderType sc t1
                         t2' <- scFirstOrderType sc t2
                         scArrayType sc t1' t2'
    FOTTuple ts -> scTupleType sc =<< traverse (scFirstOrderType sc) ts
    FOTRec tm   ->
      scRecordType sc =<< (Map.assocs <$> traverse (scFirstOrderType sc) tm)

-- | Convert a finite value to a SharedTerm.
scFiniteValue :: SharedContext -> FiniteValue -> IO Term
scFiniteValue sc fv = scFirstOrderValue sc (toFirstOrderValue fv)

-- | Convert a finite value to a SharedTerm.
scFirstOrderValue :: SharedContext -> FirstOrderValue -> IO Term
scFirstOrderValue sc fv =
  case fv of
    FOVBit b    -> scBool sc b
    FOVInt i
      | i >= 0  -> scNatToInt sc =<< scNat sc (fromInteger i)
      | True    -> scIntNeg sc =<< scNatToInt sc =<< scNat sc (fromInteger (- i))
    FOVWord n x -> scBvConst sc n x
    FOVVec t vs -> do t' <- scFirstOrderType sc t
                      vs' <- traverse (scFirstOrderValue sc) vs
                      scVector sc t' vs'
    FOVArray t1 t2 -> do t1' <- scFirstOrderType sc t1
                         t2' <- scFirstOrderType sc t2
                         scArrayType sc t1' t2'
    FOVTuple vs -> scTuple sc =<< traverse (scFirstOrderValue sc) vs
    FOVRec vm   -> scRecord sc =<< traverse (scFirstOrderValue sc) vm

-- Parsing values from lists of booleans ---------------------------------------

readFiniteValue' :: FiniteType -> S.StateT [Bool] Maybe FiniteValue
readFiniteValue' ft =
  case ft of
    FTBit      -> do bs <- S.get
                     case bs of
                       []      -> S.lift Nothing
                       b : bs' -> S.put bs' >> return (FVBit b)
    FTVec n t  -> fvVec t <$> S.replicateM (fromIntegral n) (readFiniteValue' t)
    FTTuple ts -> FVTuple <$> traverse readFiniteValue' ts
    FTRec tm   -> FVRec <$> traverse readFiniteValue' tm

readFiniteValues :: [FiniteType] -> [Bool] -> Maybe [FiniteValue]
readFiniteValues ts bs = do
  (vs, rest) <- S.runStateT (traverse readFiniteValue' ts) bs
  case rest of
    [] -> return vs
    _ -> Nothing

readFiniteValue :: FiniteType -> [Bool] -> Maybe FiniteValue
readFiniteValue t bs = do
  (v, rest) <- S.runStateT (readFiniteValue' t) bs
  case rest of
    [] -> return v
    _ -> Nothing
