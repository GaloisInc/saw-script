module Verifier.SAW.FiniteValue where

import Control.Applicative
import qualified Control.Monad.State as S
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable

import qualified Verifier.SAW.Recognizer as R
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

-- | Finite types that can be encoded as bits for a SAT/SMT solver.
data FiniteType
  = FTBit
  | FTVec Nat FiniteType
  | FTTuple [FiniteType]
  | FTRec (Map FieldName FiniteType)
  deriving (Eq, Show)

-- | Values inhabiting those finite types.
data FiniteValue
  = FVBit Bool
  | FVWord Nat Integer
  | FVVec FiniteType [FiniteValue]
  | FVTuple [FiniteValue]
  | FVRec (Map FieldName FiniteValue)
  deriving (Eq, Show)

finiteTypeOf :: FiniteValue -> FiniteType
finiteTypeOf fv =
  case fv of
    FVBit _    -> FTBit
    FVWord n _ -> FTVec n FTBit
    FVVec t vs -> FTVec (fromIntegral (length vs)) t
    FVTuple vs -> FTTuple (map finiteTypeOf vs)
    FVRec vm   -> FTRec (fmap finiteTypeOf vm)

sizeFiniteType :: FiniteType -> Int
sizeFiniteType x =
  case x of
    FTBit      -> 1
    FTVec n xs -> fromIntegral n * sizeFiniteType xs
    FTTuple xs -> sum (map sizeFiniteType xs)
    FTRec xm   -> sum (map sizeFiniteType (Map.elems xm))

asFiniteType :: SharedContext s -> SharedTerm s -> IO FiniteType
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
    _ -> fail $ "asFiniteType: unsupported argument type: " ++ show t'

-- The definitions of the next two functions depend on the encoding of
-- tuples that we want to use. Maybe it is better not to include them
-- in this library, and we should have them in the SAWScript project
-- instead.

-- | Convert a finite type to a SharedTerm.
scFiniteType :: SharedContext s -> FiniteType -> IO (SharedTerm s)
scFiniteType sc ft =
  case ft of
    FTBit      -> scBoolType sc
    FTVec n t  -> do n' <- scNat sc n
                     t' <- scFiniteType sc t
                     scVecType sc n' t'
    FTTuple ts -> scNestedTupleType sc =<< traverse (scFiniteType sc) ts
    FTRec tm   -> scRecordType sc =<< traverse (scFiniteType sc) tm -- FIXME: wrong encoding

-- | Convert a finite value to a SharedTerm.
scFiniteValue :: SharedContext s -> FiniteValue -> IO (SharedTerm s)
scFiniteValue sc fv =
  case fv of
    FVBit b    -> scBool sc b
    FVWord n x -> scBvConst sc n x
    FVVec t vs -> do t' <- scFiniteType sc t
                     vs' <- traverse (scFiniteValue sc) vs
                     scVector sc t' vs'
    FVTuple vs -> scNestedTuple sc =<< traverse (scFiniteValue sc) vs
    FVRec vm   -> scRecord sc =<< traverse (scFiniteValue sc) vm -- FIXME: wrong encoding

-- Parsing values from lists of booleans ---------------------------------------

readFiniteValue' :: FiniteType -> S.StateT [Bool] Maybe FiniteValue
readFiniteValue' ft =
  case ft of
    FTBit      -> do bs <- S.get
                     case bs of
                       []      -> S.lift Nothing
                       b : bs' -> S.put bs' >> return (FVBit b)
    FTVec n t  -> FVVec t <$> S.replicateM (fromIntegral n) (readFiniteValue' t)
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
