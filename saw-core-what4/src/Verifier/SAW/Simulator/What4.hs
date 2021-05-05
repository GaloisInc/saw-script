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
{-# LANGUAGE LambdaCase #-}
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
  ( w4Solve
  , w4SolveBasic
  , SymFnCache
  , TypedExpr(..)
  , SValue
  , Labeler(..)
  , w4Eval
  , w4EvalAny
  , w4EvalBasic
  , getLabelValues

  , w4SimulatorEval
  , NeutralTermException(..)

  , valueToSymExpr
  , symExprToValue
  ) where



import qualified Control.Arrow as A

import Data.Bits
import Data.IORef
import Data.List (genericTake)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Traversable as T
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import qualified Control.Exception as X
import Control.Monad.State as ST
import Numeric.Natural (Natural)

-- saw-core
import qualified Verifier.SAW.Recognizer as R
import qualified Verifier.SAW.Simulator as Sim
import qualified Verifier.SAW.Simulator.Prims as Prims
import Verifier.SAW.SATQuery
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.Value
import Verifier.SAW.FiniteValue (FirstOrderType(..), FirstOrderValue(..))
import Verifier.SAW.TypedAST (FieldName, ModuleMap, identName, toShortName)

-- what4
import qualified What4.Expr.Builder as B
import           What4.Expr.GroundEval
import           What4.Interface(SymExpr,Pred,SymInteger, IsExpr,
                                 IsExprBuilder,IsSymExprBuilder)
import qualified What4.Interface as W
import           What4.BaseTypes
import qualified What4.SWord as SW
import           What4.SWord (SWord(..))

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Context (Assignment)
import Data.Parameterized.Some

-- saw-core-what4
import Verifier.SAW.Simulator.What4.PosNat
import Verifier.SAW.Simulator.What4.FirstOrder
import Verifier.SAW.Simulator.What4.Panic
import Verifier.SAW.Simulator.What4.ReturnTrip

---------------------------------------------------------------------
-- empty datatype to index (open) type families
-- for this backend
data What4 (sym :: *)

-- | A What4 symbolic array where the domain and co-domain types do not appear
--   in the type
data SArray sym where
  SArray ::
    W.IsExpr (W.SymExpr sym) =>
    W.SymArray sym (Ctx.EmptyCtx Ctx.::> itp) etp ->
    SArray sym

-- type abbreviations for uniform naming
type SBool sym = Pred sym
type SInt  sym = SymInteger sym

type instance EvalM (What4 sym) = IO
type instance VBool (What4 sym) = SBool sym
type instance VWord (What4 sym) = SWord sym
type instance VInt  (What4 sym) = SInt  sym
type instance VArray (What4 sym) = SArray sym
type instance Extra (What4 sym) = What4Extra sym

type SValue sym = Value (What4 sym)

-- Constraint
type Sym sym = IsSymExprBuilder sym

---------------------------------------------------------------------

data What4Extra sym =
  SStream (Natural -> IO (SValue sym)) (IORef (Map Natural (SValue sym)))

instance Show (What4Extra sym) where
  show (SStream _ _) = "<SStream>"

---------------------------------------------------------------------
--
-- Basic primitive table for What4 data
--

prims :: forall sym.
   Sym sym => sym -> Prims.BasePrims (What4 sym)
prims sym =
  Prims.BasePrims
  { Prims.bpAsBool  = W.asConstantPred
    -- Bitvectors
  , Prims.bpUnpack  = SW.bvUnpackBE sym
  , Prims.bpPack    = SW.bvPackBE sym
  , Prims.bpBvAt    = \w i -> SW.bvAtBE sym w (toInteger i)
  , Prims.bpBvLit   = \l x -> SW.bvLit sym (toInteger l) x
  , Prims.bpBvSize  = swBvWidth
  , Prims.bpBvJoin  = SW.bvJoin   sym
  , Prims.bpBvSlice = \ a b -> SW.bvSliceBE sym (toInteger a) (toInteger b)
    -- Conditionals
  , Prims.bpMuxBool  = W.itePred sym
  , Prims.bpMuxWord  = SW.bvIte  sym
  , Prims.bpMuxInt   = W.intIte  sym
  , Prims.bpMuxExtra = muxWhat4Extra sym
    -- Booleans
  , Prims.bpTrue   = W.truePred  sym
  , Prims.bpFalse  = W.falsePred sym
  , Prims.bpNot    = W.notPred   sym
  , Prims.bpAnd    = W.andPred   sym
  , Prims.bpOr     = W.orPred    sym
  , Prims.bpXor    = W.xorPred   sym
  , Prims.bpBoolEq = W.isEq      sym
    -- Bitvector logical
  , Prims.bpBvNot  = SW.bvNot  sym
  , Prims.bpBvAnd  = SW.bvAnd  sym
  , Prims.bpBvOr   = SW.bvOr   sym
  , Prims.bpBvXor  = SW.bvXor  sym
    -- Bitvector arithmetic
  , Prims.bpBvNeg  = SW.bvNeg  sym
  , Prims.bpBvAdd  = SW.bvAdd  sym
  , Prims.bpBvSub  = SW.bvSub  sym
  , Prims.bpBvMul  = SW.bvMul  sym
  , Prims.bpBvUDiv = SW.bvUDiv sym
  , Prims.bpBvURem = SW.bvURem sym
  , Prims.bpBvSDiv = SW.bvSDiv sym
  , Prims.bpBvSRem = SW.bvSRem sym
  , Prims.bpBvLg2  = SW.bvLg2  sym
    -- Bitvector comparisons
  , Prims.bpBvEq   = SW.bvEq  sym
  , Prims.bpBvsle  = SW.bvsle sym
  , Prims.bpBvslt  = SW.bvslt sym
  , Prims.bpBvule  = SW.bvule sym
  , Prims.bpBvult  = SW.bvult sym
  , Prims.bpBvsge  = SW.bvsge sym
  , Prims.bpBvsgt  = SW.bvsgt sym
  , Prims.bpBvuge  = SW.bvuge sym
  , Prims.bpBvugt  = SW.bvugt sym
    -- Bitvector shift/rotate
  , Prims.bpBvRolInt = liftRotate sym (SW.bvRol sym)
  , Prims.bpBvRorInt = liftRotate sym (SW.bvRor sym)
  , Prims.bpBvShlInt = \z -> liftShift sym (bvShl sym z)
  , Prims.bpBvShrInt = \z -> liftShift sym (bvShr sym z)
  , Prims.bpBvRol    = SW.bvRol sym
  , Prims.bpBvRor    = SW.bvRor sym
  , Prims.bpBvShl    = bvShl sym
  , Prims.bpBvShr    = bvShr sym
    -- Bitvector misc
  , Prims.bpBvPopcount = SW.bvPopcount sym
  , Prims.bpBvCountLeadingZeros = SW.bvCountLeadingZeros sym
  , Prims.bpBvCountTrailingZeros = SW.bvCountTrailingZeros sym
  , Prims.bpBvForall = bvForall sym
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
    -- Array operations
  , Prims.bpArrayConstant = arrayConstant sym
  , Prims.bpArrayLookup = arrayLookup sym
  , Prims.bpArrayUpdate = arrayUpdate sym
  , Prims.bpArrayEq = arrayEq sym
  }


constMap :: forall sym. Sym sym => sym -> Map Ident (SValue sym)
constMap sym =
  Map.union (Prims.constMap (prims sym)) $
  Map.fromList
  [
  -- Shifts
    ("Prelude.bvShl" , bvShLOp sym)
  , ("Prelude.bvShr" , bvShROp sym)
  , ("Prelude.bvSShr", bvSShROp sym)
  -- Integers
  , ("Prelude.intToNat", intToNatOp sym)
  , ("Prelude.natToInt", natToIntOp sym)
  , ("Prelude.intToBv" , intToBvOp sym)
  , ("Prelude.bvToInt" , bvToIntOp sym)
  , ("Prelude.sbvToInt", sbvToIntOp sym)
  -- Integers mod n
  , ("Prelude.toIntMod"  , toIntModOp)
  , ("Prelude.fromIntMod", fromIntModOp sym)
  , ("Prelude.intModEq"  , intModEqOp sym)
  , ("Prelude.intModAdd" , intModBinOp sym W.intAdd)
  , ("Prelude.intModSub" , intModBinOp sym W.intSub)
  , ("Prelude.intModMul" , intModBinOp sym W.intMul)
  , ("Prelude.intModNeg" , intModUnOp sym W.intNeg)
  -- Streams
  , ("Prelude.MkStream", mkStreamOp)
  , ("Prelude.streamGet", streamGetOp sym)
  -- Misc
  , ("Prelude.expByNat", Prims.expByNatOp (prims sym))
  ]

-----------------------------------------------------------------------
-- Implementation of constMap primitives

swBvWidth :: SWord sym -> Int
swBvWidth x
  | w <= toInteger (maxBound :: Int) = fromInteger w
  | otherwise = panic "swBvWidth" ["bitvector too long", show w]
 where w = SW.bvWidth x

toBool :: SValue sym -> IO (SBool sym)
toBool (VBool b) = return b
toBool x         = fail $ unwords ["Verifier.SAW.Simulator.What4.toBool", show x]

toWord :: forall sym.
  Sym sym => sym -> SValue sym -> IO (SWord sym)
toWord _ (VWord w)    = return w
toWord sym (VVector vv) = do
  -- vec :: Vector (SBool sym))
  vec1 <- T.traverse force vv
  vec2 <- T.traverse toBool vec1
  SW.bvPackBE sym vec2
toWord _ x            = fail $ unwords ["Verifier.SAW.Simulator.What4.toWord", show x]

wordFun ::
 Sym sym => sym -> (SWord sym -> IO (SValue sym)) -> SValue sym
wordFun sym f = strictFun (\x -> f =<< toWord sym x)

valueToSymExpr :: SValue sym -> Maybe (Some (W.SymExpr sym))
valueToSymExpr = \case
  VBool b -> Just $ Some b
  VInt i -> Just $ Some i
  VWord (DBV w) -> Just $ Some w
  VArray (SArray a) -> Just $ Some a
  _ -> Nothing

symExprToValue ::
  IsExpr (SymExpr sym) =>
  W.BaseTypeRepr tp ->
  W.SymExpr sym tp ->
  Maybe (SValue sym)
symExprToValue tp expr = case tp of
  BaseBoolRepr -> Just $ VBool expr
  BaseIntegerRepr -> Just $ VInt expr
  (BaseBVRepr w) -> Just $ withKnownNat w $ VWord $ DBV expr
  (BaseArrayRepr (Ctx.Empty Ctx.:> _) _) -> Just $ VArray $ SArray expr
  _ -> Nothing

--
-- Integer bit/vector conversions
--

-- primitive intToNat : Integer -> Nat;
-- intToNat x == max 0 x
intToNatOp :: forall sym. Sym sym => sym -> SValue sym
intToNatOp sym =
  Prims.intFun "intToNat" $ \i ->
    case W.asInteger i of
      Just i'
        | 0 <= i'   -> pure (VNat (fromInteger i'))
        | otherwise -> pure (VNat 0)
      Nothing ->
        do z <- W.intLit sym 0
           pneg <- W.intLt sym i z
           i' <- W.intIte sym pneg z i
           pure (VToNat (VInt i'))

-- primitive natToInt :: Nat -> Integer;
natToIntOp :: forall sym. Sym sym => sym -> SValue sym
natToIntOp sym =
  Prims.natFun' "natToInt" $ \n ->
    VInt <$> W.intLit sym (toInteger n)

-- interpret bitvector as unsigned integer
-- primitive bvToInt : (n : Nat) -> Vec n Bool -> Integer;
bvToIntOp :: forall sym. Sym sym => sym -> SValue sym
bvToIntOp sym = constFun $ wordFun sym $ \v ->
  VInt <$> SW.bvToInteger sym v

-- interpret bitvector as signed integer
-- primitive sbvToInt : (n : Nat) -> Vec n Bool -> Integer;
sbvToIntOp :: forall sym. Sym sym => sym -> SValue sym
sbvToIntOp sym = constFun $ wordFun sym $ \v ->
   VInt <$> SW.sbvToInteger sym v

-- primitive intToBv : (n : Nat) -> Integer -> Vec n Bool;
intToBvOp :: forall sym. Sym sym => sym -> SValue sym
intToBvOp sym =
  Prims.natFun' "intToBv n" $ \n -> return $
  Prims.intFun "intToBv x" $ \(x :: SymInteger sym) ->
    VWord <$> SW.integerToBV sym x n


--
-- Shifts
--

-- | Shift left, shifting in copies of the given bit
bvShl :: IsExprBuilder sym => sym -> Pred sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvShl sym z w i =
  W.iteM SW.bvIte sym z
    (do w' <- SW.bvNot sym w
        SW.bvNot sym =<< SW.bvShl sym w' i)
    (SW.bvShl sym w i)

-- | Shift right, shifting in copies of the given bit
bvShr :: IsExprBuilder sym => sym -> Pred sym -> SWord sym -> SWord sym -> IO (SWord sym)
bvShr sym z w i =
  W.iteM SW.bvIte sym z
    (do w' <- SW.bvNot sym w
        SW.bvNot sym =<< SW.bvLshr sym w' i)
    (SW.bvLshr sym w i)

liftShift :: IsExprBuilder sym =>
  sym ->
  (SWord sym -> SWord sym -> IO (SWord sym)) ->
  SWord sym -> Integer -> IO (SWord sym)
liftShift sym f w i =
  f w =<< SW.bvLit sym (SW.bvWidth w) (i `min` SW.bvWidth w)

liftRotate :: IsExprBuilder sym =>
  sym ->
  (SWord sym -> SWord sym -> IO (SWord sym)) ->
  SWord sym -> Integer -> IO (SWord sym)
liftRotate sym f w i =
  f w =<< SW.bvLit sym (SW.bvWidth w) (i `mod` SW.bvWidth w)


-- | op : (n : Nat) -> Vec n Bool -> Nat -> Vec n Bool
bvShiftOp :: Sym sym => sym ->
             (SWord sym -> SWord sym -> IO (SWord sym)) ->
             (SWord sym -> Integer   -> IO (SWord sym)) -> SValue sym
bvShiftOp sym bvOp natOp =
  constFun  $                  -- additional argument? the size?
  wordFun sym $ \x ->            -- word to shift
  return $
  strictFun $ \y ->            -- amount to shift as a nat
    case y of
      VNat i   -> VWord <$> natOp x j
        where j = toInteger i `min` SW.bvWidth x
      VToNat v -> VWord <$> (bvOp x =<< toWord sym v)
      _        -> error $ unwords ["Verifier.SAW.Simulator.What4.bvShiftOp", show y]

-- bvShl : (w : Nat) -> Vec w Bool -> Nat -> Vec w Bool;
bvShLOp :: forall sym. Sym sym => sym -> SValue sym
bvShLOp sym = bvShiftOp sym (SW.bvShl sym)
                    (liftShift sym (SW.bvShl sym))

-- bvShR : (w : Nat) -> Vec w Bool -> Nat -> Vec w Bool;
bvShROp :: forall sym. Sym sym => sym -> SValue sym
bvShROp sym = bvShiftOp sym (SW.bvLshr sym)
                    (liftShift sym (SW.bvLshr sym))

-- bvSShR : (w : Nat) -> Vec w Bool -> Nat -> Vec w Bool;
bvSShROp :: forall sym. Sym sym => sym -> SValue sym
bvSShROp sym = bvShiftOp sym (SW.bvAshr sym)
                     (liftShift sym (SW.bvAshr sym))

bvForall :: W.IsSymExprBuilder sym =>
  sym -> Natural -> (SWord sym -> IO (Pred sym)) -> IO (Pred sym)
bvForall sym n f =
  do let indexSymbol = W.safeSymbol "i"
     case mkNatRepr n of
        Some w
          | Just LeqProof <- testLeq (knownNat @1) w ->
            withKnownNat w $ do
              i <- W.freshBoundVar sym indexSymbol $ W.BaseBVRepr w
              body <- f . DBV $ W.varExpr sym i
              W.forallPred sym i body
          | otherwise -> f ZBV

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

toIntModOp :: SValue sym
toIntModOp =
  Prims.natFun' "toIntMod" $ \n -> pure $
  Prims.intFun "toIntMod" $ \x -> pure $
  VIntMod n x

fromIntModOp :: IsExprBuilder sym => sym -> SValue sym
fromIntModOp sym =
  Prims.natFun $ \n -> return $
  Prims.intModFun "fromIntModOp" $ \x ->
  VInt <$> (W.intMod sym x =<< W.intLit sym (toInteger n))

intModEqOp :: IsExprBuilder sym => sym -> SValue sym
intModEqOp sym =
  Prims.natFun $ \n -> return $
  Prims.intModFun "intModEqOp" $ \x -> return $
  Prims.intModFun "intModEqOp" $ \y ->
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
  Prims.intModFun "intModBinOp x" $ \x -> return $
  Prims.intModFun "intModBinOp y" $ \y ->
  VIntMod n <$> (normalizeIntMod sym n =<< f sym x y)

intModUnOp ::
  IsExprBuilder sym => sym ->
  (sym -> SInt sym -> IO (SInt sym)) -> SValue sym
intModUnOp sym f =
  Prims.natFun $ \n -> return $
  Prims.intModFun "intModUnOp" $ \x ->
  VIntMod n <$> (normalizeIntMod sym n =<< f sym x)

normalizeIntMod :: IsExprBuilder sym => sym -> Natural -> SInt sym -> IO (SInt sym)
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
streamGetOp :: forall sym. Sym sym => sym -> SValue sym
streamGetOp sym =
  constFun $
  strictFun $ \xs -> return $
  strictFun $ \case
    VNat n -> lookupSStream xs n
    VToNat w ->
      do ilv <- toWord sym w
         selectV sym (lazyMux @sym (muxBVal sym)) ((2 ^ SW.bvWidth ilv) - 1) (lookupSStream xs) ilv
    v -> Prims.panic "streamGetOp" ["Expected Nat value", show v]

lookupSStream :: SValue sym -> Natural -> IO (SValue sym)
lookupSStream (VExtra (SStream f r)) n = do
   m <- readIORef r
   case Map.lookup n m of
     Just v  -> return v
     Nothing -> do v <- f n
                   writeIORef r (Map.insert n v m)
                   return v
lookupSStream _ _ = fail "expected Stream"


muxBVal :: forall sym. Sym sym =>
  sym -> SBool sym -> SValue sym -> SValue sym -> IO (SValue sym)
muxBVal sym = Prims.muxValue (prims sym)

muxWhat4Extra :: forall sym. Sym sym =>
  sym -> SBool sym -> What4Extra sym -> What4Extra sym -> IO (What4Extra sym)
muxWhat4Extra sym c x y =
  do let f i = do xi <- lookupSStream (VExtra x) i
                  yi <- lookupSStream (VExtra y) i
                  muxBVal sym c xi yi
     r <- newIORef Map.empty
     return (SStream f r)


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
selectV :: forall sym b.
  Sym sym =>
  sym ->
  (SBool sym -> IO b -> IO b -> IO b) -> Natural -> (Natural -> IO b) -> SWord sym -> IO b
selectV sym merger maxValue valueFn vx =
  case SW.bvAsUnsignedInteger vx of
    Just i  -> valueFn (fromInteger i :: Natural)
    Nothing -> impl (swBvWidth vx) 0
  where
    impl :: Int -> Natural -> IO b
    impl _ x | x > maxValue || x < 0 = valueFn maxValue
    impl 0 y = valueFn y
    impl i y = do
      p <- SW.bvAtBE sym vx (toInteger j)
      merger p (impl j (y `setBit` j)) (impl j y) where j = i - 1

instance Show (SArray sym) where
  show (SArray arr) = show $ W.printSymExpr arr

arrayConstant ::
  W.IsSymExprBuilder sym =>
  sym ->
  TValue (What4 sym) ->
  SValue sym ->
  IO (SArray sym)
arrayConstant sym ity elm
  | Just (Some idx_repr) <- valueAsBaseType ity
  , Just (Some elm_expr) <- valueToSymExpr elm =
    SArray <$> W.constantArray sym (Ctx.Empty Ctx.:> idx_repr) elm_expr
  | otherwise =
    panic "Verifier.SAW.Simulator.What4.Panic.arrayConstant" ["argument type mismatch"]

arrayLookup ::
  W.IsSymExprBuilder sym =>
  sym ->
  SArray sym ->
  SValue sym ->
  IO (SValue sym)
arrayLookup sym arr idx
  | SArray arr_expr <- arr
  , Just (Some idx_expr) <- valueToSymExpr idx
  , W.BaseArrayRepr (Ctx.Empty Ctx.:> idx_repr) elm_repr <- W.exprType arr_expr
  , Just Refl <- testEquality idx_repr (W.exprType idx_expr) = do
    elm_expr <- W.arrayLookup sym arr_expr (Ctx.Empty Ctx.:> idx_expr)
    maybe
      (panic "Verifier.SAW.Simulator.What4.Panic.arrayLookup" ["argument type mismatch"])
      return
      (symExprToValue elm_repr elm_expr)
  | otherwise =
    panic "Verifier.SAW.Simulator.What4.Panic.arrayLookup" ["argument type mismatch"]

arrayUpdate ::
  W.IsSymExprBuilder sym =>
  sym ->
  SArray sym ->
  SValue sym ->
  SValue sym ->
  IO (SArray sym)
arrayUpdate sym arr idx elm
  | SArray arr_expr <- arr
  , Just (Some idx_expr) <- valueToSymExpr idx
  , Just (Some elm_expr) <- valueToSymExpr elm
  , W.BaseArrayRepr (Ctx.Empty Ctx.:> idx_repr) elm_repr <- W.exprType arr_expr
  , Just Refl <- testEquality idx_repr (W.exprType idx_expr)
  , Just Refl <- testEquality elm_repr (W.exprType elm_expr) =
    SArray <$> W.arrayUpdate sym arr_expr (Ctx.Empty Ctx.:> idx_expr) elm_expr
  | otherwise =
    panic "Verifier.SAW.Simulator.What4.Panic.arrayUpdate" ["argument type mismatch"]

arrayEq ::
  W.IsSymExprBuilder sym =>
  sym ->
  SArray sym ->
  SArray sym ->
  IO (W.Pred sym)
arrayEq sym lhs_arr rhs_arr
  | SArray lhs_arr_expr <- lhs_arr
  , SArray rhs_arr_expr <- rhs_arr
  , W.BaseArrayRepr (Ctx.Empty Ctx.:> lhs_idx_repr) lhs_elm_repr <- W.exprType lhs_arr_expr
  , W.BaseArrayRepr (Ctx.Empty Ctx.:> rhs_idx_repr) rhs_elm_repr <- W.exprType rhs_arr_expr
  , Just Refl <- testEquality lhs_idx_repr rhs_idx_repr
  , Just Refl <- testEquality lhs_elm_repr rhs_elm_repr =
    W.arrayEq sym lhs_arr_expr rhs_arr_expr
  | otherwise =
    panic "Verifier.SAW.Simulator.What4.Panic.arrayEq" ["argument type mismatch"]

----------------------------------------------------------------------
-- | A basic symbolic simulator/evaluator: interprets a saw-core Term as
-- a symbolic value

w4SolveBasic ::
  forall sym. IsSymExprBuilder sym =>
  sym ->
  SharedContext ->
  Map Ident (SValue sym) {- ^ additional primitives -} ->
  Map VarIndex (SValue sym) {- ^ bindings for ExtCns values -} ->
  IORef (SymFnCache sym) {- ^ cache for uninterpreted function symbols -} ->
  Set VarIndex {- ^ 'unints' Constants in this list are kept uninterpreted -} ->
  Term {- ^ term to simulate -} ->
  IO (SValue sym)
w4SolveBasic sym sc addlPrims ecMap ref unintSet t =
  do m <- scGetModuleMap sc
     let extcns (EC ix nm ty)
            | Just v <- Map.lookup ix ecMap = return v
            | otherwise = parseUninterpreted sym ref (mkUnintApp (Text.unpack (toShortName nm) ++ "_" ++ show ix)) ty
     let uninterpreted ec
           | Set.member (ecVarIndex ec) unintSet = Just (extcns ec)
           | otherwise                           = Nothing
     cfg <- Sim.evalGlobal m (constMap sym `Map.union` addlPrims) extcns uninterpreted
     Sim.evalSharedTerm cfg t


----------------------------------------------------------------------
-- Uninterpreted function cache

data SymFnWrapper sym :: Ctx.Ctx BaseType -> * where
  SymFnWrapper :: !(W.SymFn sym args ret) -> SymFnWrapper sym (args Ctx.::> ret)

type SymFnCache sym = Map W.SolverSymbol (MapF (Assignment BaseTypeRepr) (SymFnWrapper sym))

lookupSymFn ::
  W.SolverSymbol -> Assignment BaseTypeRepr args -> BaseTypeRepr ty ->
  SymFnCache sym -> Maybe (W.SymFn sym args ty)
lookupSymFn s args ty cache =
  do m <- Map.lookup s cache
     SymFnWrapper fn <- MapF.lookup (Ctx.extend args ty) m
     return fn

insertSymFn ::
  W.SolverSymbol -> Assignment BaseTypeRepr args -> BaseTypeRepr ty ->
  W.SymFn sym args ty -> SymFnCache sym -> SymFnCache sym
insertSymFn s args ty fn = Map.alter upd s
  where
    upd Nothing = Just (MapF.singleton (Ctx.extend args ty) (SymFnWrapper fn))
    upd (Just m) = Just (MapF.insert (Ctx.extend args ty) (SymFnWrapper fn) m)

mkSymFn ::
  forall sym args ret. (IsSymExprBuilder sym) =>
  sym -> IORef (SymFnCache sym) ->
  String -> Assignment BaseTypeRepr args -> BaseTypeRepr ret ->
  IO (W.SymFn sym args ret)
mkSymFn sym ref nm args ret =
  do let s = W.safeSymbol nm
     cache <- readIORef ref
     case lookupSymFn s args ret cache of
       Just fn -> return fn
       Nothing ->
         do fn <- W.freshTotalUninterpFn sym s args ret
            writeIORef ref (insertSymFn s args ret fn cache)
            return fn

----------------------------------------------------------------------
-- Given a constant nm of (saw-core) type ty, construct an uninterpreted
-- constant with that type.
-- Importantly: The types of these uninterpreted values are *not*
-- limited to What4 BaseTypes or FirstOrderTypes.

parseUninterpreted ::
  forall sym.
  (IsSymExprBuilder sym) =>
  sym -> IORef (SymFnCache sym) ->
  UnintApp (SymExpr sym) ->
  TValue (What4 sym) -> IO (SValue sym)
parseUninterpreted sym ref app ty =
  case ty of
    VPiType _ f
      -> return $
         strictFun $ \x -> do
           app' <- applyUnintApp sym app x
           t2 <- f (ready x)
           parseUninterpreted sym ref app' t2

    VBoolType
      -> VBool <$> mkUninterpreted sym ref app BaseBoolRepr

    VIntType
      -> VInt  <$> mkUninterpreted sym ref app BaseIntegerRepr

    VIntModType n
      -> VIntMod n <$> mkUninterpreted sym ref app BaseIntegerRepr

    -- 0 width bitvector is a constant
    VVecType 0 VBoolType
      -> return $ VWord ZBV

    VVecType n VBoolType
      | Just (Some (PosNat w)) <- somePosNat n
      -> (VWord . DBV) <$> mkUninterpreted sym ref app (BaseBVRepr w)

    VVecType n ety
      ->  do xs <- sequence $
                  [ parseUninterpreted sym ref (suffixUnintApp ("_a" ++ show i) app) ety
                  | i <- [0 .. n-1] ]
             return (VVector (V.fromList (map ready xs)))

    VArrayType ity ety
      | Just (Some idx_repr) <- valueAsBaseType ity
      , Just (Some elm_repr) <- valueAsBaseType ety
      -> (VArray . SArray) <$>
          mkUninterpreted sym ref app (BaseArrayRepr (Ctx.Empty Ctx.:> idx_repr) elm_repr)

    VUnitType
      -> return VUnit

    VPairType ty1 ty2
      -> do x1 <- parseUninterpreted sym ref (suffixUnintApp "_L" app) ty1
            x2 <- parseUninterpreted sym ref (suffixUnintApp "_R" app) ty2
            return (VPair (ready x1) (ready x2))

    VRecordType elem_tps
      -> (VRecordValue <$>
          mapM (\(f,tp) ->
                 (f,) <$> ready <$>
                 parseUninterpreted sym ref (suffixUnintApp ("_" ++ Text.unpack f) app) tp) elem_tps)

    _ -> fail $ "could not create uninterpreted symbol of type " ++ show ty


mkUninterpreted ::
  forall sym t. (IsSymExprBuilder sym) =>
  sym -> IORef (SymFnCache sym) ->
  UnintApp (SymExpr sym) ->
  BaseTypeRepr t ->
  IO (SymExpr sym t)
mkUninterpreted sym ref (UnintApp nm args tys) ret =
  do fn <- mkSymFn sym ref nm tys ret
     W.applySymFn sym fn args

-- | A value of type @UnintApp f@ represents an uninterpreted function
-- with the given 'String' name, applied to a list of argument values
-- paired with a representation of their types. The context of
-- argument types is existentially quantified.
data UnintApp f =
  forall args. UnintApp String (Assignment f args) (Assignment BaseTypeRepr args)

-- | Extract the string from an 'UnintApp'.
stringOfUnintApp :: UnintApp f -> String
stringOfUnintApp (UnintApp s _ _) = s

-- | Make an 'UnintApp' with the given name and no arguments.
mkUnintApp :: String -> UnintApp f
mkUnintApp nm = UnintApp nm Ctx.empty Ctx.empty

-- | Add a suffix to the function name of an 'UnintApp'.
suffixUnintApp :: String -> UnintApp f -> UnintApp f
suffixUnintApp s (UnintApp nm args tys) = UnintApp (nm ++ s) args tys

-- | Extend an 'UnintApp' with an additional argument.
extendUnintApp :: UnintApp f -> f ty -> BaseTypeRepr ty -> UnintApp f
extendUnintApp (UnintApp nm xs tys) x ty =
  UnintApp nm (Ctx.extend xs x) (Ctx.extend tys ty)

-- | Flatten an 'SValue' to a sequence of components, each of which is
-- a symbolic value of a base type (e.g. word or boolean), and add
-- them to the list of arguments of the given 'UnintApp'. If the
-- 'SValue' contains any values built from data constructors, then
-- encode them as suffixes on the function name of the 'UnintApp'.
applyUnintApp ::
  forall sym.
  (W.IsExprBuilder sym) =>
  sym ->
  UnintApp (SymExpr sym) ->
  SValue sym ->
  IO (UnintApp (SymExpr sym))
applyUnintApp sym app0 v =
  case v of
    VUnit                     -> return app0
    VPair x y                 -> do app1 <- applyUnintApp sym app0 =<< force x
                                    app2 <- applyUnintApp sym app1 =<< force y
                                    return app2
    VRecordValue elems        -> foldM (applyUnintApp sym) app0 =<< traverse (force . snd) elems
    VVector xv                -> foldM (applyUnintApp sym) app0 =<< traverse force xv
    VBool sb                  -> return (extendUnintApp app0 sb BaseBoolRepr)
    VInt si                   -> return (extendUnintApp app0 si BaseIntegerRepr)
    VIntMod 0 si              -> return (extendUnintApp app0 si BaseIntegerRepr)
    VIntMod n si              -> do n' <- W.intLit sym (toInteger n)
                                    si' <- W.intMod sym si n'
                                    return (extendUnintApp app0 si' BaseIntegerRepr)
    VWord (DBV sw)            -> return (extendUnintApp app0 sw (W.exprType sw))
    VArray (SArray sa)        -> return (extendUnintApp app0 sa (W.exprType sa))
    VWord ZBV                 -> return app0
    VCtorApp i xv             -> foldM (applyUnintApp sym) app' =<< traverse force xv
                                   where app' = suffixUnintApp ("_" ++ identName i) app0
    VNat n                    -> return (suffixUnintApp ("_" ++ show n) app0)
    TValue (suffixTValue -> Just s)
                              -> return (suffixUnintApp s app0)
    VFun _ ->
      fail $
      "Cannot create uninterpreted higher-order function " ++
      show (stringOfUnintApp app0)
    _ ->
      fail $
      "Cannot create uninterpreted function " ++
      show (stringOfUnintApp app0) ++
      " with argument " ++ show v


------------------------------------------------------------

w4Solve :: forall sym.
  IsSymExprBuilder sym =>
  sym ->
  SharedContext ->
  SATQuery ->
  IO ([ExtCns Term], [FirstOrderType], [Labeler sym], SBool sym)
w4Solve sym sc satq =
  do t <- satQueryAsTerm sc satq
     let varList  = Map.toList (satVariables satq)
     let argNames = map fst varList
     let argTys   = map snd varList
     vars <- evalStateT (traverse (traverse (newVarFOT sym)) varList) 0
     let lbls     = map (fst . snd) vars
     let varMap   = Map.fromList [ (ecVarIndex ec, v) | (ec, (_,v)) <- vars ]
     ref <- newIORef Map.empty
     bval <- w4SolveBasic sym sc mempty varMap ref (satUninterp satq) t
     case bval of
       VBool v -> return (argNames, argTys, lbls, v)
       _ -> fail $ "w4Solve: non-boolean result type. " ++ show bval

--
-- Pull out argument types until bottoming out at a non-Pi type
--
argTypes :: IsSymExprBuilder sym => TValue (What4 sym) -> IO [TValue (What4 sym)]
argTypes v =
  case v of
    VPiType v1 f ->
      do x <- delay (fail "argTypes: unsupported dependent SAW-Core type")
         v2 <- f x
         vs <- argTypes v2
         return (v1 : vs)
    _ -> return []

--
-- Convert a saw-core type expression to a FirstOrder type expression
--
vAsFirstOrderType :: forall sym. IsSymExprBuilder sym => TValue (What4 sym) -> Maybe FirstOrderType
vAsFirstOrderType v =
  case v of
    VBoolType
      -> return FOTBit
    VIntType
      -> return FOTInt
    VIntModType n
      -> return (FOTIntMod n)
    VVecType n v2
      -> FOTVec n <$> vAsFirstOrderType v2
    VArrayType iv ev
      -> FOTArray <$> vAsFirstOrderType iv <*> vAsFirstOrderType ev
    VUnitType
      -> return (FOTTuple [])
    VPairType v1 v2
      -> do t1 <- vAsFirstOrderType v1
            t2 <- vAsFirstOrderType v2
            case t2 of
              FOTTuple ts -> return (FOTTuple (t1 : ts))
              _ -> return (FOTTuple [t1, t2])
    VRecordType tps
      -> (FOTRec <$> Map.fromList <$>
          mapM (\(f,tp) -> (f,) <$> vAsFirstOrderType tp) tps)
    _ -> Nothing

valueAsBaseType :: IsSymExprBuilder sym => TValue (What4 sym) -> Maybe (Some W.BaseTypeRepr)
valueAsBaseType v = fotToBaseType =<< vAsFirstOrderType v

------------------------------------------------------------------------------

-- | Generate a new symbolic value (a variable) from a given first-order-type


data TypedExpr sym where
  TypedExpr :: BaseTypeRepr ty -> SymExpr sym ty -> TypedExpr sym


-- | Create a fresh constant with the given name and type.
mkConstant ::
  forall sym ty.
  (IsSymExprBuilder sym) =>
  sym -> String -> BaseTypeRepr ty -> IO (SymExpr sym ty)
mkConstant sym name ty = W.freshConstant sym (W.safeSymbol name) ty

-- | Generate a new variable from a given BaseType

freshVar :: forall sym ty. IsSymExprBuilder sym =>
  sym -> BaseTypeRepr ty -> String -> IO (TypedExpr sym)
freshVar sym ty str =
  do c <- mkConstant sym str ty
     return (TypedExpr ty c)

nextId :: StateT Int IO String
nextId = ST.get >>= (\s-> modify (+1) >> return ("x" ++ show s))


newVarsForType :: forall sym. IsSymExprBuilder sym =>
  sym ->
  IORef (SymFnCache sym) ->
  TValue (What4 sym) -> String -> StateT Int IO (Maybe (Labeler sym), SValue sym)
newVarsForType sym ref v nm =
  case vAsFirstOrderType v of
    Just fot -> do
      do (te,sv) <- newVarFOT sym fot
         return (Just te, sv)

    Nothing ->
      do sv <- lift $ parseUninterpreted sym ref (mkUnintApp nm) v
         return (Nothing, sv)

myfun ::(Map FieldName (Labeler sym, SValue sym)) -> (Map FieldName (Labeler sym), Map FieldName (SValue sym))
myfun = fmap fst A.&&& fmap snd

data Labeler sym
  = BaseLabel (TypedExpr sym)
  | ZeroWidthBVLabel
  | IntModLabel Natural (SymInteger sym)
  | VecLabel (Vector (Labeler sym))
  | TupleLabel (Vector (Labeler sym))
  | RecLabel (Map FieldName (Labeler sym))


newVarFOT :: forall sym. IsSymExprBuilder sym =>
   sym -> FirstOrderType -> StateT Int IO (Labeler sym, SValue sym)

newVarFOT sym (FOTTuple ts) = do
  (labels,vals) <- V.unzip <$> traverse (newVarFOT sym) (V.fromList ts)
  args <- traverse (return . ready) (V.toList vals)
  return (TupleLabel labels, vTuple args)

newVarFOT _sym (FOTVec 0 FOTBit)
  = return (ZeroWidthBVLabel, VWord ZBV)

newVarFOT sym (FOTVec n tp)
  | tp /= FOTBit
  = do (labels,vals) <- V.unzip <$> V.replicateM (fromIntegral n) (newVarFOT sym tp)
       args <- traverse @Vector @(StateT Int IO) (return . ready) vals
       return (VecLabel labels, VVector args)

newVarFOT sym (FOTRec tm)
  = do (labels, vals) <- myfun <$> traverse (newVarFOT sym) tm
       args <- traverse (return . ready) (vals :: (Map FieldName (SValue sym)))
       return (RecLabel labels, vRecord args)

newVarFOT sym (FOTIntMod n)
  = do nm <- nextId
       let r = BaseIntegerRepr
       si <- lift $ mkConstant sym nm r
       return (IntModLabel n si, VIntMod n si)

newVarFOT sym fot
  | Just (Some r) <- fotToBaseType fot
  = do nm <- nextId
       te <- lift $ freshVar sym r nm
       sv <- lift $ typedToSValue te
       return (BaseLabel te, sv)
  | otherwise
  = fail ("Cannot create What4 variable of type: " ++ show fot)


typedToSValue :: (IsExpr (SymExpr sym)) => TypedExpr sym -> IO (SValue sym)
typedToSValue (TypedExpr ty expr) =
  maybe (fail ("Cannot handle " ++ show ty)) return $ symExprToValue ty expr

getLabelValues ::
  forall sym t.
  (SymExpr sym ~ B.Expr t) =>
  GroundEvalFn t -> Labeler sym -> IO FirstOrderValue
getLabelValues f =
  \case
    TupleLabel labels ->
      FOVTuple <$> traverse (getLabelValues f) (V.toList labels)
    VecLabel labels ->
      FOVVec vty <$> traverse (getLabelValues f) (V.toList labels)
      where vty = error "TODO: compute vector type, or just store it"
    RecLabel labels ->
      FOVRec <$> traverse (getLabelValues f) labels
    IntModLabel n x ->
      FOVIntMod n <$> groundEval f x
    ZeroWidthBVLabel -> pure $ FOVWord 0 0
    BaseLabel (TypedExpr ty bv) ->
      do gv <- groundEval f bv
         case (groundToFOV ty gv) of
           Left err  -> fail err
           Right fov -> pure fov

----------------------------------------------------------------------
-- Evaluation through crucible-saw backend


-- | Simplify a saw-core term by evaluating it through the saw backend
-- of what4.
w4EvalAny ::
  forall n st fs.
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  SharedContext ->
  Map Ident (SValue (B.ExprBuilder n st fs)) -> Set VarIndex -> Term ->
  IO ([String], ([Maybe (Labeler (B.ExprBuilder n st fs))], SValue (B.ExprBuilder n st fs)))
w4EvalAny sym st sc ps unintSet t =
  do modmap <- scGetModuleMap sc
     ref <- newIORef Map.empty
     let eval = w4EvalBasic sym st sc modmap ps ref unintSet
     ty <- eval =<< scTypeOf sc t

     -- get the names of the arguments to the function
     let lamNames = map (Text.unpack . fst) (fst (R.asLambdaList t))
     let varNames = [ "var" ++ show (i :: Integer) | i <- [0 ..] ]
     let argNames = zipWith (++) varNames (map ("_" ++) lamNames ++ repeat "")

     -- and their types
     argTs <- argTypes (toTValue ty)

     -- construct symbolic expressions for the variables
     vars' <-
       flip evalStateT 0 $
       sequence (zipWith (newVarsForType sym ref) argTs argNames)

     -- symbolically evaluate
     bval <- eval t

     -- apply and existentially quantify
     let (bvs, vars) = unzip vars'
     let vars'' = fmap ready vars
     bval' <- applyAll bval vars''

     return (argNames, (bvs, bval'))

w4Eval ::
  forall n st fs.
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  SharedContext ->
  Map Ident (SValue (B.ExprBuilder n st fs)) -> Set VarIndex -> Term ->
  IO ([String], ([Maybe (Labeler (B.ExprBuilder n st fs))], SBool (B.ExprBuilder n st fs)))
w4Eval sym st sc ps uintSet t =
  do (argNames, (bvs, bval)) <- w4EvalAny sym st sc ps uintSet t
     case bval of
       VBool b -> return (argNames, (bvs, b))
       _ -> fail $ "w4Eval: non-boolean result type. " ++ show bval

-- | Simplify a saw-core term by evaluating it through the saw backend
-- of what4.
w4EvalBasic ::
  forall n st fs.
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  SharedContext ->
  ModuleMap ->
  Map Ident (SValue (B.ExprBuilder n st fs)) {- ^ additional primitives -} ->
  IORef (SymFnCache (B.ExprBuilder n st fs)) {- ^ cache for uninterpreted function symbols -} ->
  Set VarIndex {- ^ 'unints' Constants in this list are kept uninterpreted -} ->
  Term {- ^ term to simulate -} ->
  IO (SValue (B.ExprBuilder n st fs))
w4EvalBasic sym st sc m addlPrims ref unintSet t =
  do let extcns tf (EC ix nm ty) =
           do trm <- ArgTermConst <$> scTermF sc tf
              parseUninterpretedSAW sym st sc ref trm
                 (mkUnintApp (Text.unpack (toShortName nm) ++ "_" ++ show ix)) ty
     let uninterpreted tf ec
           | Set.member (ecVarIndex ec) unintSet = Just (extcns tf ec)
           | otherwise                           = Nothing
     cfg <- Sim.evalGlobal' m (constMap sym `Map.union` addlPrims) extcns uninterpreted
     Sim.evalSharedTerm cfg t


-- | Evaluate a saw-core term to a What4 value for the purposes of
--   using it as an input for symbolic simulation.  This will evaluate
--   primitives, but will cancel evaluation and return the associated
--   'NameInfo' if it encounters a constant value with an 'ExtCns'
--   that is not accepted by the filter.
w4SimulatorEval ::
  forall n st fs.
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  SharedContext ->
  ModuleMap ->
  Map Ident (SValue (B.ExprBuilder n st fs)) {- ^ additional primitives -} ->
  IORef (SymFnCache (B.ExprBuilder n st fs)) {- ^ cache for uninterpreted function symbols -} ->
  (ExtCns (TValue (What4 (B.ExprBuilder n st fs))) -> Bool)
    {- ^ Filter for constant values.  True means unfold, false means halt evaluation. -} ->
  Term {- ^ term to simulate -} ->
  IO (Either NameInfo (SValue (B.ExprBuilder n st fs)))
w4SimulatorEval sym st sc m addlPrims ref constantFilter t =
  do let extcns tf (EC ix nm ty) =
           do trm <- ArgTermConst <$> scTermF sc tf
              parseUninterpretedSAW sym st sc ref trm (mkUnintApp (Text.unpack (toShortName nm) ++ "_" ++ show ix)) ty
     let uninterpreted _tf ec =
          if constantFilter ec then Nothing else Just (X.throwIO (NeutralTermEx (ecName ec)))
     res <- X.try $ do
              cfg <- Sim.evalGlobal' m (constMap sym `Map.union` addlPrims) extcns uninterpreted
              Sim.evalSharedTerm cfg t
     case res of
       Left (NeutralTermEx nmi) -> pure (Left nmi)
       Right x -> pure (Right x)

data NeutralTermException = NeutralTermEx NameInfo deriving Show
instance X.Exception NeutralTermException

-- | Given a constant nm of (saw-core) type ty, construct an
-- uninterpreted constant with that type. The 'Term' argument should
-- be an open term, which should have the designated return type when
-- the local variables have the corresponding types from the
-- 'Assignment'.
parseUninterpretedSAW ::
  forall n st fs.
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  SharedContext ->
  IORef (SymFnCache (B.ExprBuilder n st fs)) ->
  ArgTerm {- ^ representation of function applied to arguments -} ->
  UnintApp (SymExpr (B.ExprBuilder n st fs)) ->
  TValue (What4 (B.ExprBuilder n st fs)) {- ^ return type -} ->
  IO (SValue (B.ExprBuilder n st fs))
parseUninterpretedSAW sym st sc ref trm app ty =
  case ty of
    VPiType t1 f
      -> return $
         strictFun $ \x -> do
           app' <- applyUnintApp sym app x
           arg <- mkArgTerm sc t1 x
           let trm' = ArgTermApply trm arg
           t2 <- f (ready x)
           parseUninterpretedSAW sym st sc ref trm' app' t2

    VBoolType
      -> VBool <$> mkUninterpretedSAW sym st ref trm app BaseBoolRepr

    VIntType
      -> VInt  <$> mkUninterpretedSAW sym st ref trm app BaseIntegerRepr

    -- 0 width bitvector is a constant
    VVecType 0 VBoolType
      -> return $ VWord ZBV

    VVecType n VBoolType
      | Just (Some (PosNat w)) <- somePosNat n
      -> (VWord . DBV) <$> mkUninterpretedSAW sym st ref trm app (BaseBVRepr w)

    VVecType n ety | n >= 0
      ->  do ety' <- termOfTValue sc ety
             let mkElem i =
                   do let trm' = ArgTermAt n ety' trm i
                      let app' = suffixUnintApp ("_a" ++ show i) app
                      parseUninterpretedSAW sym st sc ref trm' app' ety
             xs <- traverse mkElem (genericTake n [0 ..])
             return (VVector (V.fromList (map ready xs)))

    VArrayType ity ety
      | Just (Some idx_repr) <- valueAsBaseType ity
      , Just (Some elm_repr) <- valueAsBaseType ety
      -> (VArray . SArray) <$>
          mkUninterpretedSAW sym st ref trm app (BaseArrayRepr (Ctx.Empty Ctx.:> idx_repr) elm_repr)

    VUnitType
      -> return VUnit

    VPairType ty1 ty2
      -> do let trm1 = ArgTermPairLeft trm
            let trm2 = ArgTermPairRight trm
            x1 <- parseUninterpretedSAW sym st sc ref trm1 (suffixUnintApp "_L" app) ty1
            x2 <- parseUninterpretedSAW sym st sc ref trm2 (suffixUnintApp "_R" app) ty2
            return (VPair (ready x1) (ready x2))

    _ -> fail $ "could not create uninterpreted symbol of type " ++ show ty

mkUninterpretedSAW ::
  forall n st fs t.
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  IORef (SymFnCache (B.ExprBuilder n st fs)) ->
  ArgTerm ->
  UnintApp (SymExpr (B.ExprBuilder n st fs)) ->
  BaseTypeRepr t ->
  IO (SymExpr (B.ExprBuilder n st fs) t)
mkUninterpretedSAW sym st ref trm (UnintApp nm args tys) ret =
  do fn <- mkSymFn sym ref nm tys ret
     sawRegisterSymFunInterp st fn (reconstructArgTerm trm)
     W.applySymFn sym fn args

-- | An 'ArgTerm' is a description of how to reassemble a saw-core
-- term from a list of the atomic components it is composed of.
data ArgTerm
  = ArgTermVar
  | ArgTermBVZero -- ^ scBvNat 0 0
  | ArgTermVector Term [ArgTerm] -- ^ element type, elements
  | ArgTermUnit
  | ArgTermPair ArgTerm ArgTerm
  | ArgTermRecord [(FieldName, ArgTerm)]
  | ArgTermConst Term
  | ArgTermApply ArgTerm ArgTerm
  | ArgTermAt Natural Term ArgTerm Natural
    -- ^ length, element type, list, index
  | ArgTermPairLeft ArgTerm
  | ArgTermPairRight ArgTerm

-- | Reassemble a saw-core term from an 'ArgTerm' and a list of parts.
-- The length of the list should be equal to the number of
-- 'ArgTermVar' constructors in the 'ArgTerm'.
reconstructArgTerm :: ArgTerm -> SharedContext -> [Term] -> IO Term
reconstructArgTerm atrm sc ts =
  do (t, unused) <- parse atrm ts
     unless (null unused) $ fail "reconstructArgTerm: too many function arguments"
     return t
  where
    parse :: ArgTerm -> [Term] -> IO (Term, [Term])
    parse at ts0 =
      case at of
        ArgTermVar ->
          case ts0 of
            x : ts1 -> return (x, ts1)
            [] -> fail "reconstructArgTerm: too few function arguments"
        ArgTermBVZero ->
          do z <- scNat sc 0
             x <- scBvNat sc z z
             return (x, ts0)
        ArgTermVector ty ats ->
          do (xs, ts1) <- parseList ats ts0
             x <- scVector sc ty xs
             return (x, ts1)
        ArgTermUnit ->
          do x <- scUnitValue sc
             return (x, ts0)
        ArgTermPair at1 at2 ->
          do (x1, ts1) <- parse at1 ts0
             (x2, ts2) <- parse at2 ts1
             x <- scPairValue sc x1 x2
             return (x, ts2)
        ArgTermRecord flds ->
          do let (tags, ats) = unzip flds
             (xs, ts1) <- parseList ats ts0
             x <- scRecord sc (Map.fromList (zip tags xs))
             return (x, ts1)
        ArgTermConst x ->
          do return (x, ts0)
        ArgTermApply at1 at2 ->
          do (x1, ts1) <- parse at1 ts0
             (x2, ts2) <- parse at2 ts1
             x <- scApply sc x1 x2
             return (x, ts2)
        ArgTermAt n ty at1 i ->
          do n' <- scNat sc n
             (x1, ts1) <- parse at1 ts0
             i' <- scNat sc i
             x <- scAt sc n' ty x1 i'
             return (x, ts1)
        ArgTermPairLeft at1 ->
          do (x1, ts1) <- parse at1 ts0
             x <- scPairLeft sc x1
             return (x, ts1)
        ArgTermPairRight at1 ->
          do (x1, ts1) <- parse at1 ts0
             x <- scPairRight sc x1
             return (x, ts1)

    parseList :: [ArgTerm] -> [Term] -> IO ([Term], [Term])
    parseList [] ts0 = return ([], ts0)
    parseList (at : ats) ts0 =
      do (x, ts1) <- parse at ts0
         (xs, ts2) <- parseList ats ts1
         return (x : xs, ts2)

-- | Given a type and value encoded as 'SValue's, construct an
-- 'ArgTerm' that builds a term of that type from local variables with
-- base types. The number of 'ArgTermVar' constructors should match
-- the number of arguments appended by 'applyUnintApp'.
mkArgTerm :: SharedContext -> TValue (What4 sym) -> SValue sym -> IO ArgTerm
mkArgTerm sc ty val =
  case (ty, val) of
    (VBoolType, VBool _) -> return ArgTermVar
    (VIntType, VInt _)   -> return ArgTermVar
    (_, VWord ZBV)       -> return ArgTermBVZero     -- 0-width bitvector is a constant
    (_, VWord (DBV _))   -> return ArgTermVar
    (VUnitType, VUnit)   -> return ArgTermUnit

    (VVecType _ ety, VVector vv) ->
      do vs <- traverse force (V.toList vv)
         xs <- traverse (mkArgTerm sc ety) vs
         ety' <- termOfTValue sc ety
         return (ArgTermVector ety' xs)

    (VPairType ty1 ty2, VPair v1 v2) ->
      do x1 <- mkArgTerm sc ty1 =<< force v1
         x2 <- mkArgTerm sc ty2 =<< force v2
         return (ArgTermPair x1 x2)

    (VRecordType tys, VRecordValue flds) | map fst tys == map fst flds ->
      do let tags = map fst tys
         vs <- traverse (force . snd) flds
         xs <- sequence [ mkArgTerm sc t v | (t, v) <- zip (map snd tys) vs ]
         return (ArgTermRecord (zip tags xs))

    (_, VCtorApp i vv) ->
      do xs <- traverse (termOfSValue sc <=< force) (V.toList vv)
         x <- scCtorApp sc i xs
         return (ArgTermConst x)

    (_, TValue tval) ->
      do x <- termOfTValue sc tval
         pure (ArgTermConst x)

    _ -> fail $ "could not create uninterpreted function argument of type " ++ show ty

termOfTValue :: SharedContext -> TValue (What4 sym) -> IO Term
termOfTValue sc val =
  case val of
    VBoolType -> scBoolType sc
    VIntType -> scIntegerType sc
    VUnitType -> scUnitType sc
    VVecType n a ->
      do n' <- scNat sc n
         a' <- termOfTValue sc a
         scVecType sc n' a'
    VPairType a b
      -> do a' <- termOfTValue sc a
            b' <- termOfTValue sc b
            scPairType sc a' b'
    VRecordType flds
      -> do flds' <- traverse (traverse (termOfTValue sc)) flds
            scRecordType sc flds'
    _ -> fail $ "termOfTValue: " ++ show val

termOfSValue :: SharedContext -> SValue sym -> IO Term
termOfSValue sc val =
  case val of
    VUnit -> scUnitValue sc
    VNat n
      -> scNat sc n
    TValue tv -> termOfTValue sc tv
    _ -> fail $ "termOfSValue: " ++ show val
