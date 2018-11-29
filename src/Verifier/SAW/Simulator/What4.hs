------------------------------------------------------------------------
-- |
-- Module      : Verifier.SAW.Simulator.What4
-- Copyright   : Galois, Inc. 2012-2015
-- License     : BSD3
-- Maintainer  : sweirich@galois.com
-- Stability   : experimental
-- Portability : non-portable (language extensions)
--
-- A symbolic simulator for saw-core terms using What4.
-- (This module is derived from Verifier.SAW.Simulator.SBV)
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds#-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- WithKnownNat
{-# OPTIONS_GHC -Wno-warnings-deprecations #-}


module Verifier.SAW.Simulator.What4
  (
    w4Solve,
    TypedExpr(..),
    SValue,
    Labeler(..)
  ) where



import qualified Control.Arrow as A

import Data.Bits
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Traversable as T
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad.State as ST


import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.Simulator as Sim
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.Value
import Verifier.SAW.TypedAST (FieldName, ModuleMap, identName)
import Verifier.SAW.FiniteValue (FirstOrderType(..))

import           What4.Interface(SymExpr,Pred,SymInteger, IsExpr,
                                 IsExprBuilder,IsSymExprBuilder)
import qualified What4.Interface as W
import           What4.BaseTypes

import Data.Reflection (Given(..))
import Data.Parameterized.Some

import Verifier.SAW.Simulator.What4.SWord
import Verifier.SAW.Simulator.What4.PosNat
import Verifier.SAW.Simulator.What4.FirstOrder


---------------------------------------------------------------------
-- empty datatype to index (open) type families
-- for this backend
data What4 (sym :: *)

-- type abbreviations for uniform naming
type SBool sym = Pred sym
type SInt  sym = SymInteger sym

type instance EvalM (What4 sym) = IO
type instance VBool (What4 sym) = SBool sym
type instance VWord (What4 sym) = SWord sym
type instance VInt  (What4 sym) = SInt  sym
type instance Extra (What4 sym) = What4Extra sym

type SValue sym = Value (What4 sym)

-- Constraint
type Sym sym = (Given sym, IsExprBuilder sym)

---------------------------------------------------------------------

data What4Extra sym =
  SStream (Integer -> IO (SValue sym)) (IORef (Map Integer (SValue sym)))

instance Show (What4Extra sym) where
  show (SStream _ _) = "<SStream>"

---------------------------------------------------------------------
--
-- Basic primitive table for What4 data
--

prims :: forall sym. (Sym sym) =>
   Prims.BasePrims (What4 sym)
prims =
  let sym :: sym = given in
  Prims.BasePrims
  { Prims.bpAsBool  = W.asConstantPred
    -- Bitvectors
  , Prims.bpUnpack  = bvUnpack sym
  , Prims.bpPack    = bvPack   sym
  , Prims.bpBvAt    = bvAt     sym
  , Prims.bpBvLit   = bvLit    sym
  , Prims.bpBvSize  = intSizeOf
  , Prims.bpBvJoin  = bvJoin   sym
  , Prims.bpBvSlice = bvSlice  sym
    -- Conditionals
  , Prims.bpMuxBool  = W.itePred sym
  , Prims.bpMuxWord  = bvIte     sym
  , Prims.bpMuxInt   = W.intIte  sym
  , Prims.bpMuxExtra = extraFn
    -- Booleans
  , Prims.bpTrue   = W.truePred  sym
  , Prims.bpFalse  = W.falsePred sym
  , Prims.bpNot    = W.notPred   sym
  , Prims.bpAnd    = W.andPred   sym
  , Prims.bpOr     = W.orPred    sym
  , Prims.bpXor    = W.xorPred   sym
  , Prims.bpBoolEq = W.isEq      sym
    -- Bitvector logical
  , Prims.bpBvNot  = bvNot  sym
  , Prims.bpBvAnd  = bvAnd  sym
  , Prims.bpBvOr   = bvOr   sym
  , Prims.bpBvXor  = bvXor  sym
    -- Bitvector arithmetic
  , Prims.bpBvNeg  = bvNeg  sym
  , Prims.bpBvAdd  = bvAdd  sym
  , Prims.bpBvSub  = bvSub  sym
  , Prims.bpBvMul  = bvMul  sym
  , Prims.bpBvUDiv = bvUDiv sym
  , Prims.bpBvURem = bvURem sym
  , Prims.bpBvSDiv = bvSDiv sym
  , Prims.bpBvSRem = bvSRem sym
  , Prims.bpBvLg2  = bvLg2  sym
    -- Bitvector comparisons
  , Prims.bpBvEq   = bvEq  sym
  , Prims.bpBvsle  = bvsle sym
  , Prims.bpBvslt  = bvslt sym
  , Prims.bpBvule  = bvule sym
  , Prims.bpBvult  = bvult sym
  , Prims.bpBvsge  = bvsge sym
  , Prims.bpBvsgt  = bvsgt sym
  , Prims.bpBvuge  = bvuge sym
  , Prims.bpBvugt  = bvugt sym
    -- Bitvector shift/rotate
  , Prims.bpBvRolInt = bvRolInt sym
  , Prims.bpBvRorInt = bvRorInt sym
  , Prims.bpBvShlInt = bvShlInt sym
  , Prims.bpBvShrInt = bvShrInt sym
  , Prims.bpBvRol    = bvRol sym
  , Prims.bpBvRor    = bvRor sym
  , Prims.bpBvShl    = bvShl sym
  , Prims.bpBvShr    = bvShr sym
    -- Integer operations
  , Prims.bpIntAbs = W.intAbs sym
  , Prims.bpIntAdd = W.intAdd sym
  , Prims.bpIntSub = W.intSub sym
  , Prims.bpIntMul = W.intMul sym
  , Prims.bpIntDiv = W.intDiv sym
  , Prims.bpIntMod = W.intMod sym
  , Prims.bpIntNeg = W.intNeg sym
  , Prims.bpIntEq  = W.intEq sym
  , Prims.bpIntLe  = W.intLe sym
  , Prims.bpIntLt  = W.intLt sym
  , Prims.bpIntMin = intMin  sym
  , Prims.bpIntMax = intMax  sym
  }


constMap :: forall sym. (Sym sym) => Map Ident (SValue sym)
constMap =
  Map.union (Prims.constMap prims) $
  Map.fromList
  [
  -- Shifts
    ("Prelude.bvShl" , bvShLOp)
  , ("Prelude.bvShr" , bvShROp)
  , ("Prelude.bvSShr", bvSShROp)
  -- Integers
  --XXX , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  -- Integers mod n
  , ("Prelude.IntMod"    , constFun VIntType)
  , ("Prelude.toIntMod"  , constFun (VFun force))
  , ("Prelude.fromIntMod", fromIntModOp sym)
  , ("Prelude.intModEq"  , intModEqOp sym)
  , ("Prelude.intModAdd" , intModBinOp sym W.intAdd)
  , ("Prelude.intModSub" , intModBinOp sym W.intSub)
  , ("Prelude.intModMul" , intModBinOp sym W.intMul)
  , ("Prelude.intModNeg" , intModUnOp sym W.intNeg)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp)
  , ("Prelude.bvStreamGet", bvStreamGetOp)
  ]
  where sym = given :: sym

-----------------------------------------------------------------------
-- Implementation of constMap primitives

toBool :: SValue sym -> IO (SBool sym)
toBool (VBool b) = return b
toBool x         = fail $ unwords ["Verifier.SAW.Simulator.What4.toBool", show x]

toWord :: forall sym. (Sym sym) =>
          SValue sym -> IO (SWord sym)
toWord (VWord w)    = return w
toWord (VVector vv) = do
  -- vec :: Vector (SBool sym))
  vec1 <- T.traverse force vv
  vec2 <- T.traverse toBool vec1
  bvPack (given :: sym) vec2
toWord x            = fail $ unwords ["Verifier.SAW.Simulator.What4.toWord", show x]

wordFun :: (IsExprBuilder sym, Given sym) =>
           (SWord sym -> IO (SValue sym)) -> SValue sym
wordFun f = strictFun (\x -> f =<< toWord x)

--
-- Integer bit/vector conversions
--

-- primitive natToInt :: Nat -> Integer;
natToIntOp :: forall sym. (Sym sym) => SValue sym
natToIntOp =
  Prims.natFun' "natToInt" $ \n ->
    VInt <$> W.intLit (given :: sym) (toInteger n)

-- interpret bitvector as unsigned integer
-- primitive bvToInt :: (n::Nat) -> bitvector n -> Integer;
bvToIntOp :: forall sym. (Sym sym) => SValue sym
bvToIntOp = constFun $ wordFun $ \(v :: SWord sym) -> do
  VInt <$> bvToInteger (given :: sym) v

-- interpret bitvector as signed integer
-- primitive sbvToInt :: (n::Nat) -> bitvector n -> Integer;
sbvToIntOp :: forall sym. (Sym sym) => SValue sym
sbvToIntOp = constFun $ wordFun $ \v -> do
   VInt <$> sbvToInteger (given :: sym) v

-- primitive intToBv :: (n::Nat) -> Integer -> bitvector n;
intToBvOp :: forall sym. (Sym sym) => SValue sym
intToBvOp =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \(x :: SymInteger sym) ->
    VWord <$> integerToBV (given :: sym) x n


--
-- Shifts
--

-- | op :: (n :: Nat) -> bitvector n -> Nat -> bitvector n
bvShiftOp :: (Sym sym) =>
             (SWord sym -> SWord sym -> IO (SWord sym)) ->
             (SWord sym -> Integer   -> IO (SWord sym)) -> SValue sym
bvShiftOp bvOp natOp =
  constFun  $                  -- additional argument? the size?
  wordFun   $ \x ->            -- word to shift
  return $
  strictFun $ \y ->            -- amount to shift as a nat
    case y of
      VNat i   -> VWord <$> natOp x j
        where j = i `min` toInteger (intSizeOf x)
      VToNat v -> VWord <$> (bvOp x =<< toWord v)
      _        -> error $ unwords ["Verifier.SAW.Simulator.What4.bvShiftOp", show y]

-- bvShl :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShLOp :: forall sym. (Sym sym) => SValue sym
bvShLOp = bvShiftOp (bvShl    given (W.falsePred @sym given))
                    (bvShlInt given (W.falsePred @sym given))

-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvShROp :: forall sym. (Sym sym) => SValue sym
bvShROp = bvShiftOp (bvShr    given (W.falsePred @sym given))
                    (bvShrInt given (W.falsePred @sym given))


-- bvShR :: (w :: Nat) -> bitvector w -> Nat -> bitvector w;
bvSShROp :: forall sym. (Sym sym) => SValue sym
bvSShROp = bvShiftOp (bvSShr    given (W.falsePred @sym given))
                     (bvSShrInt given (W.falsePred @sym given))


--
-- missing integer operations
--

intMin :: (IsExprBuilder sym) => sym -> SInt sym -> SInt sym -> IO (SInt sym)
intMin sym i1 i2 = do
  p <- W.intLt sym i1 i2
  W.intIte sym p i1 i2

intMax :: (IsExprBuilder sym) => sym -> SInt sym -> SInt sym -> IO (SInt sym)
intMax sym i1 i2 = do
  p <- W.intLt sym i1 i2
  W.intIte sym p i2 i1

------------------------------------------------------------
-- Integers mod n

fromIntModOp :: IsExprBuilder sym => sym -> SValue sym
fromIntModOp sym =
  Prims.natFun $ \n -> return $
  Prims.intFun "fromIntModOp" $ \x ->
  VInt <$> (W.intMod sym x =<< W.intLit sym (toInteger n))

intModEqOp :: IsExprBuilder sym => sym -> SValue sym
intModEqOp sym =
  Prims.natFun $ \n -> return $
  Prims.intFun "intModEqOp" $ \x -> return $
  Prims.intFun "intModEqOp" $ \y ->
  do modulus <- W.intLit sym (toInteger n)
     d <- W.intSub sym x y
     r <- W.intMod sym d modulus
     z <- W.intLit sym 0
     VBool <$> W.intEq sym r z

intModBinOp ::
  IsExprBuilder sym => sym ->
  (sym -> SInt sym -> SInt sym -> IO (SInt sym)) -> SValue sym
intModBinOp sym f =
  Prims.natFun $ \n -> return $
  Prims.intFun "intModBinOp x" $ \x -> return $
  Prims.intFun "intModBinOp y" $ \y ->
  VInt <$> (normalizeIntMod sym n =<< f sym x y)

intModUnOp ::
  IsExprBuilder sym => sym ->
  (sym -> SInt sym -> IO (SInt sym)) -> SValue sym
intModUnOp sym f =
  Prims.natFun $ \n -> return $
  Prims.intFun "intModUnOp" $ \x ->
  VInt <$> (normalizeIntMod sym n =<< f sym x)

normalizeIntMod :: IsExprBuilder sym => sym -> Nat -> SInt sym -> IO (SInt sym)
normalizeIntMod sym n x =
  case W.asInteger x of
    Nothing -> return x
    Just i -> W.intLit sym (i `mod` toInteger n)

------------------------------------------------------------
-- Stream operations

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: SValue sym
mkStreamOp =
  constFun $
  strictFun $ \f -> do
    r <- newIORef Map.empty
    return $ VExtra (SStream (\n -> apply f (ready (VNat n))) r)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: SValue sym
streamGetOp =
  constFun $
  strictFun $ \xs -> return $
  Prims.natFun'' "streamGetOp" $ \n -> lookupSStream xs (toInteger n)

-- bvStreamGet :: (a :: sort 0) -> (w :: Nat) -> Stream a -> bitvector w -> a;
bvStreamGetOp :: forall sym. (IsExpr (SymExpr sym), Sym sym) => SValue sym
bvStreamGetOp =
  constFun $
  constFun $
  strictFun $ \xs -> return $
  wordFun $ \ilv ->
  selectV (lazyMux @sym muxBVal) ((2 ^ intSizeOf ilv) - 1) (lookupSStream xs) ilv

lookupSStream :: SValue sym -> Integer -> IO (SValue sym)
lookupSStream (VExtra (SStream f r)) n = do
   m <- readIORef r
   case Map.lookup n m of
     Just v  -> return v
     Nothing -> do v <- f n
                   writeIORef r (Map.insert n v m)
                   return v
lookupSStream _ _ = fail "expected Stream"


muxBVal :: forall sym. (Sym sym) =>
  SBool sym -> SValue sym -> SValue sym -> IO (SValue sym)
muxBVal = Prims.muxValue prims

extraFn :: SBool sym -> What4Extra sym -> What4Extra sym -> IO (What4Extra sym)
extraFn _ _ _ = error "iteOp: malformed arguments (extraFn)"


-- | Lifts a strict mux operation to a lazy mux
lazyMux :: (IsExpr (SymExpr sym)) =>
  (SBool sym  -> a -> a -> IO a) -> (SBool sym -> IO a -> IO a -> IO a)
lazyMux muxFn c tm fm =
  case W.asConstantPred c of
    Just True  -> tm
    Just False -> fm
    Nothing    -> do
      t <- tm
      f <- fm
      muxFn c t f

-- selectV merger maxValue valueFn index returns valueFn v when index has value v
-- if index is greater than maxValue, it returns valueFn maxValue. Use the ite op from merger.
selectV :: forall sym a b. (Sym sym, Ord a, Num a, Bits a) =>
  (SBool sym -> IO b -> IO b -> IO b) -> a -> (a -> IO b) -> SWord sym -> IO b
selectV merger maxValue valueFn vx =
  case bvAsUnsignedInteger vx of
    Just i  -> valueFn (fromIntegral i)
    Nothing -> impl (intSizeOf vx) 0
  where
    impl :: Int -> a -> IO b
    impl _ x | x > maxValue || x < 0 = valueFn maxValue
    impl 0 y = valueFn y
    impl i y = do
      p <- bvAt (given :: sym) vx j
      merger p (impl j (y `setBit` j)) (impl j y) where j = i - 1

-----------------------------------------------------------------------
-- | A basic symbolic simulator/evaluator: interprets a saw-core Term as
-- a symbolic value

w4SolveBasic :: forall sym. (Given sym, IsSymExprBuilder sym) =>
  ModuleMap
  -> Map Ident (SValue sym)
  -- ^ additional primatives
  -> [String]
  -- ^ 'unints' Constants in this list are kept uninterpreted
  -> Term
  -- ^ term to simulate
  -> IO (SValue sym)
w4SolveBasic m addlPrims unints t = do
  let unintSet = Set.fromList unints
  let uninterpreted nm ty
        | Set.member nm unintSet = Just $ parseUninterpreted nm ty
        | otherwise              = Nothing
  cfg <- Sim.evalGlobal m (constMap `Map.union` addlPrims)
         (const parseUninterpreted)
         uninterpreted
  Sim.evalSharedTerm cfg t


------------------------------------------------------------
-- Given a constant nm of (saw-core) type ty, construct an uninterpreted
-- constant with that type.
-- Importantly: The types of these uninterpreted values are *not*
-- limited to What4 BaseTypes or FirstOrderTypes.

parseUninterpreted :: forall sym. (Given sym, IsSymExprBuilder sym) =>
  String -> SValue sym -> IO (SValue sym)
parseUninterpreted nm ty =
  case ty of
    VPiType _ rng
      -> return $
         strictFun $ \x -> do
           suffix <- flattenSValue x
           t2 <- rng (ready x)
           parseUninterpreted (nm ++ suffix) t2

    VBoolType
      -> VBool <$> mkUninterpreted @sym nm BaseBoolRepr

    VIntType
      -> VInt  <$> mkUninterpreted @sym nm BaseIntegerRepr

    -- 0 width bitvector is a constant
    VVecType (VNat 0) VBoolType
      -> return $ VWord ZBV

    VVecType (VNat n) VBoolType
      | Just (Some (PosNat nr)) <- somePosNat n
      -> (VWord . DBV) <$> mkUninterpreted @sym nm (BaseBVRepr nr)

    VVecType (VNat 0) _
      -> fail "TODO: 0-width non-bitvectors unsupported"

    VVecType (VNat n) ety
      | Just (Some (PosNat _)) <- somePosNat n
      ->  do xs <- sequence $
                  [ parseUninterpreted (nm ++ "@" ++ show i) ety
                  | i <- [0 .. n-1] ]
             return (VVector (V.fromList (map ready xs)))

    VUnitType
      -> return VUnit

    VPairType ty1 ty2
      -> do x1 <- parseUninterpreted (nm ++ ".L") ty1
            x2 <- parseUninterpreted (nm ++ ".R") ty2
            return (VPair (ready x1) (ready x2))

    VEmptyType
      -> return VEmpty

    (VFieldType f ty1 ty2)
      -> do x1 <- parseUninterpreted (nm ++ ".L") ty1
            x2 <- parseUninterpreted (nm ++ ".R") ty2
            return (VField f (ready x1) x2)

    (VRecordType elem_tps)
      -> (VRecordValue <$>
          mapM (\(f,tp) ->
                 (f,) <$> ready <$>
                 parseUninterpreted (nm ++ "." ++ f) tp) elem_tps)


    _ -> fail $ "could not create uninterpreted symbol of type " ++ show ty


-- NOTE: Ambiguous type. Must include a type application to call
-- this function
mkUninterpreted :: forall sym t. (Given sym, IsSymExprBuilder sym) =>
  String -> BaseTypeRepr t -> IO (SymExpr sym t)
mkUninterpreted nm rep =
  case W.userSymbol nm of
    Left err -> fail $ show err ++ ":Cannot create uninterpreted constant " ++ nm
    Right s  -> W.freshConstant (given :: sym) s rep



-- Flatten an SValue to an encoded string
-- encoded as a String.
flattenSValue :: SValue sym -> IO String
flattenSValue v = do
  case v of
    VUnit                     -> return ("")
    VPair x y                 -> do sx <- flattenSValue =<< force x
                                    sy <- flattenSValue =<< force y
                                    return (sx ++ sy)
    VEmpty                    -> return ("")
    VField _ x y              -> do sx <- flattenSValue =<< force x
                                    sy <- flattenSValue y
                                    return (sx ++ sy)
    VRecordValue elems        -> do sxs <- mapM (flattenSValue <=< force . snd) elems
                                    return (concat sxs)
    VVector (V.toList -> ts)  -> do ss <- traverse (force >=> flattenSValue) ts
                                    return (concat ss)
    VBool _sb                 -> return ("")
    VWord _sw                 -> return ("")
    VCtorApp i (V.toList->ts) -> do ss <- traverse (force >=> flattenSValue) ts
                                    return ("_" ++ identName i ++ concat ss)
    VNat n                    -> return ("_" ++ show n)
    _ -> fail $ "Could not create argument for " ++ show v

------------------------------------------------------------

w4Solve :: forall sym. (Given sym, IsSymExprBuilder sym) =>
         SharedContext
      -> Map Ident (SValue sym)
      -> [String]
      -> Term
      -> IO ([String], ([Maybe (Labeler sym)], SBool sym))
w4Solve sc ps unints t = do
  modmap <- scGetModuleMap sc
  let eval = w4SolveBasic modmap ps unints
  ty <- eval =<< scTypeOf sc t

  -- get the names of the arguments to the function
  let argNames = map fst (fst (R.asLambdaList t))
  let moreNames = [ "var" ++ show (i :: Integer) | i <- [0 ..] ]

  -- and their types
  argTs <- asPredType ty

  -- construct symbolic expressions for the variables
  vars' <-
    flip evalStateT 0 $
    sequence (zipWith newVarsForType argTs (argNames ++ moreNames))

  -- symbolically evaluate
  bval <- eval t

  -- apply and existentially quantify
  let (bvs, vars) = unzip vars'
  let vars'' = fmap ready vars
  bval' <- applyAll bval vars''

  prd <- case bval' of
           VBool b -> return b
           _ -> fail $ "solve: non-boolean result type. " ++ show bval'
  return (argNames, (bvs, prd))


--
-- Pull out argument types until bottoming out at a bool type
--
asPredType :: IsSymExprBuilder sv => SValue sv -> IO [SValue sv]
asPredType v =
  case v of
    VBoolType -> return []
    VPiType v1 f ->
      do v2 <- f (error "asPredType: unsupported dependent SAW-Core type")
         vs <- asPredType v2
         return (v1 : vs)
    _ -> fail $ "non-boolean result type: " ++ show v

--
-- Convert a saw-core type expression to a FirstOrder type expression
--
vAsFirstOrderType :: forall sv. IsSymExprBuilder sv => SValue sv -> Maybe FirstOrderType
vAsFirstOrderType v =
  case v of
    VBoolType
      -> return FOTBit
    VIntType
      -> return FOTInt
    VVecType (VNat n) v2
      -> FOTVec (fromInteger n) <$> vAsFirstOrderType v2
    VUnitType
      -> return (FOTTuple [])
    VPairType v1 v2
      -> do t1 <- vAsFirstOrderType v1
            t2 <- vAsFirstOrderType v2
            case t2 of
              FOTTuple ts -> return (FOTTuple (t1 : ts))
              _ -> Nothing
    VEmptyType
      -> return (FOTRec Map.empty)
    VFieldType k v1 v2
      -> do t1 <- vAsFirstOrderType v1
            t2 <- vAsFirstOrderType v2
            case t2 of
              FOTRec tm -> return (FOTRec (Map.insert k t1 tm))
              _ -> Nothing
    (asVTupleType -> Just vs)
      -> FOTTuple <$> mapM vAsFirstOrderType vs
    VRecordType tps
      -> (FOTRec <$> Map.fromList <$>
          mapM (\(f,tp) -> (f,) <$> vAsFirstOrderType tp) tps)
    _ -> Nothing

------------------------------------------------------------------------------

-- | Generate a new symbolic value (a variable) from a given first-order-type


data TypedExpr sym where
  TypedExpr :: BaseTypeRepr ty -> SymExpr sym ty -> TypedExpr sym


-- | Generate a new variable from a given BaseType

freshVar :: forall sym ty. (IsSymExprBuilder sym, Given sym) =>
  BaseTypeRepr ty -> String -> IO (TypedExpr sym)
freshVar ty str =
  case W.userSymbol str of
    Right solverSymbol -> do
      c <- W.freshConstant (given :: sym) solverSymbol ty
      return (TypedExpr ty c)
    Left _ ->
      fail $ "Cannot create solver symbol " ++ str

nextId :: StateT Int IO String
nextId = ST.get >>= (\s-> modify (+1) >> return ("x" ++ show s))


newVarsForType :: forall sym. (Given sym, IsSymExprBuilder sym) =>
  SValue sym -> String -> StateT Int IO (Maybe (Labeler sym), SValue sym)
newVarsForType v nm =
  case vAsFirstOrderType v of
    Just fot -> do
      do (te,sv) <- newVarFOT fot
         return (Just te, sv)

    Nothing ->
      do sv <- lift $ parseUninterpreted nm v
         return (Nothing, sv)

myfun ::(Map String (Labeler sym, SValue sym)) -> (Map String (Labeler sym), Map String (SValue sym))
myfun = fmap fst A.&&& fmap snd

data Labeler sym
   = BaseLabel  (TypedExpr sym)
   | VecLabel   (Vector (Labeler sym))
   | TupleLabel (Vector (Labeler sym))
   | RecLabel   (Map FieldName (Labeler sym))


newVarFOT :: forall sym. (IsSymExprBuilder sym, Given sym) =>
   FirstOrderType -> StateT Int IO (Labeler sym, SValue sym)

newVarFOT (FOTTuple ts) = do
  (labels,vals) <- V.unzip <$> traverse newVarFOT (V.fromList ts)
  args <- traverse (return . ready) (V.toList vals)
  return (TupleLabel labels, vTuple args)

newVarFOT (FOTVec n tp)
  | tp /= FOTBit
  = do (labels,vals) <- V.unzip <$> V.replicateM (fromIntegral n) (newVarFOT tp)
       args <- traverse @Vector @(StateT Int IO) (return . ready) vals
       return (VecLabel labels, VVector args)

newVarFOT (FOTRec tm)
  = do (labels, vals) <- myfun <$> traverse newVarFOT tm
       args <- traverse (return . ready) (vals :: (Map String (SValue sym)))
       return (RecLabel labels, vRecord args)

newVarFOT fot
  | Some r <- fotToBaseType fot
  = do nm <- nextId
       te <- lift $ freshVar r nm
       sv <- lift $ typedToSValue te
       return (BaseLabel te, sv)



typedToSValue :: (IsExpr (SymExpr sym)) => TypedExpr sym -> IO (SValue sym)
typedToSValue (TypedExpr ty expr) =
  case ty of
    BaseBoolRepr         -> return $ VBool expr
    BaseIntegerRepr      -> return $ VInt  expr
    (BaseBVRepr w)       -> return $ withKnownNat w $ VWord (DBV expr)
    _                    -> fail "Cannot handle"
