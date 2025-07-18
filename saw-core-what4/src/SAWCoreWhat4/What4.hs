------------------------------------------------------------------------
-- |
-- Module      : SAWCoreWhat4.What4
-- Copyright   : Galois, Inc. 2012-2015
-- License     : BSD3
-- Maintainer  : sweirich@galois.com
-- Stability   : experimental
-- Portability : non-portable (language extensions)
--
-- A symbolic simulator for saw-core terms using What4.
-- (This module is derived from SAWCoreSBV.SBV)
------------------------------------------------------------------------

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


module SAWCoreWhat4.What4
  ( w4Solve
  , w4SolveBasic
  , SymFnCache
  , TypedExpr(..)
  , SValue
  , SPrim
  , Labeler(..)
  , w4Eval
  , w4EvalAny
  , w4EvalBasic
  , getLabelValues

  , w4EvalTerm
  , w4SimulatorEval
  , NeutralTermException(..)

  , valueToSymExpr
  , symExprToValue
  ) where



import qualified Control.Arrow as A

import Data.Bits
import Data.IORef
import Data.Kind (Type)
import Data.List (genericTake)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Traversable as T
import qualified Control.Exception as X
import Control.Monad ((<=<), foldM, unless)
import Control.Monad.State as ST (MonadState(..), StateT(..), evalStateT, modify)
import Control.Monad.Trans.Class (MonadTrans(..))
import Numeric.Natural (Natural)

-- saw-core
import qualified SAWCore.Recognizer as R
import qualified SAWCore.Simulator as Sim
import qualified SAWCore.Simulator.Prims as Prims
import SAWCore.SATQuery
import SAWCore.SharedTerm
import SAWCore.Simulator.Value
import SAWCore.FiniteValue (FirstOrderType(..), FirstOrderValue(..))
import SAWCore.Module (ModuleMap, ResolvedName(..), ctorName, lookupVarIndexInMap)
import SAWCore.Name (toAbsoluteName, toShortName)
import SAWCore.Term.Functor (FieldName)

-- what4
import qualified What4.Expr.Builder as B
import           What4.Expr.GroundEval
import           What4.Interface(SymExpr,Pred,SymInteger, IsExpr, SymFnWrapper(..),
                                 IsExprBuilder,IsSymExprBuilder, BoundVar)
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
import SAWCoreWhat4.PosNat
import SAWCoreWhat4.FirstOrder
import SAWCoreWhat4.Panic
import SAWCoreWhat4.ReturnTrip

---------------------------------------------------------------------
-- empty datatype to index (open) type families
-- for this backend
data What4 (sym :: Type)

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
type SPrim sym  = Prims.Prim (What4 sym)

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
  { Prims.bpIsSymbolicEvaluator = True
  , Prims.bpAsBool  = W.asConstantPred
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
  , Prims.bpMuxArray = arrayIte sym
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
  , Prims.bpIntDiv = intDiv sym
  , Prims.bpIntMod = intMod sym
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
  , Prims.bpArrayCopy = arrayCopy sym
  , Prims.bpArraySet = arraySet sym
  , Prims.bpArrayRangeEq = arrayRangeEq sym
  }


constMap :: forall sym. Sym sym => sym -> Map Ident (SPrim sym)
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
  | otherwise = croak
 where w = SW.bvWidth x
       croak = panic "swBvWidth" [
           "Bitvector too long: width " <> Text.pack (show w) <>
               ", value " <> Text.pack (show x)
        ]

toBool :: SValue sym -> IO (SBool sym)
toBool (VBool b) = return b
toBool x         = fail $ unwords ["SAWCoreWhat4.What4.toBool", show x]

toWord :: forall sym.
  Sym sym => sym -> SValue sym -> IO (SWord sym)
toWord _ (VWord w)    = return w
toWord sym (VVector vv) = do
  -- vec :: Vector (SBool sym))
  vec1 <- T.traverse force vv
  vec2 <- T.traverse toBool vec1
  SW.bvPackBE sym vec2
toWord _ x            = fail $ unwords ["SAWCoreWhat4.What4.toWord", show x]

wordFun ::
 Sym sym => sym -> (SWord sym -> SPrim sym) -> SPrim sym
wordFun sym = Prims.wordFun (SW.bvPackBE sym)

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
intToNatOp :: forall sym. Sym sym => sym -> SPrim sym
intToNatOp sym =
  Prims.intFun $ \i ->
  Prims.Prim $
    case W.asInteger i of
      Just i'
        | 0 <= i'   -> pure (VNat (fromInteger i'))
        | otherwise -> pure (VNat 0)
      Nothing ->
        do z <- W.intLit sym 0
           pneg <- W.intLt sym i z
           i' <- W.intIte sym pneg z i
           pure (VIntToNat (VInt i'))

-- primitive natToInt :: Nat -> Integer;
natToIntOp :: forall sym. Sym sym => sym -> SPrim sym
natToIntOp sym =
  Prims.natFun $ \n ->
    Prims.Prim (VInt <$> W.intLit sym (toInteger n))

-- interpret bitvector as unsigned integer
-- primitive bvToInt : (n : Nat) -> Vec n Bool -> Integer;
bvToIntOp :: forall sym. Sym sym => sym -> SPrim sym
bvToIntOp sym =
  Prims.constFun $
  wordFun sym $ \v ->
    Prims.Prim (VInt <$> SW.bvToInteger sym v)

-- interpret bitvector as signed integer
-- primitive sbvToInt : (n : Nat) -> Vec n Bool -> Integer;
sbvToIntOp :: forall sym. Sym sym => sym -> SPrim sym
sbvToIntOp sym =
  Prims.constFun $
  wordFun sym $ \v ->
    Prims.Prim (VInt <$> SW.sbvToInteger sym v)

-- primitive intToBv : (n : Nat) -> Integer -> Vec n Bool;
intToBvOp :: forall sym. Sym sym => sym -> SPrim sym
intToBvOp sym =
  Prims.natFun $ \n ->
  Prims.intFun $ \(x :: SymInteger sym) ->
    Prims.Prim (VWord <$> SW.integerToBV sym x n)


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
             (SWord sym -> Integer   -> IO (SWord sym)) -> SPrim sym
bvShiftOp sym bvOp natOp =
  Prims.constFun  $                  -- additional argument? the size?
  wordFun sym $ \x ->                -- word to shift
  Prims.strictFun $ \y ->            -- amount to shift as a nat
  Prims.Prim $
    case y of
      VNat i   -> VWord <$> natOp x j
        where j = toInteger i `min` SW.bvWidth x
      VBVToNat _ v -> VWord <$> (bvOp x =<< toWord sym v)
      _        -> error $ unwords ["SAWCoreWhat4.What4.bvShiftOp", show y]

-- bvShl : (w : Nat) -> Vec w Bool -> Nat -> Vec w Bool;
bvShLOp :: forall sym. Sym sym => sym -> SPrim sym
bvShLOp sym = bvShiftOp sym (SW.bvShl sym)
                    (liftShift sym (SW.bvShl sym))

-- bvShR : (w : Nat) -> Vec w Bool -> Nat -> Vec w Bool;
bvShROp :: forall sym. Sym sym => sym -> SPrim sym
bvShROp sym = bvShiftOp sym (SW.bvLshr sym)
                    (liftShift sym (SW.bvLshr sym))

-- bvSShR : (w : Nat) -> Vec w Bool -> Nat -> Vec w Bool;
bvSShROp :: forall sym. Sym sym => sym -> SPrim sym
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

-- NB: What4's division operation provides SMT-LIB's Euclidean division, which
-- doesn't match the round-to-neg-infinity semantics of Cryptol, so we have to
-- do some work to get the desired semantics.
intDiv ::
  IsExprBuilder sym =>
  sym ->
  SymExpr sym BaseIntegerType ->
  SymExpr sym BaseIntegerType ->
  IO (SymExpr sym BaseIntegerType)
intDiv sym x y = do
  neg <- W.intLt sym y =<< W.intLit sym 0
  case W.asConstantPred neg of
    Just False -> W.intDiv sym x y
    Just True  ->
       do xneg <- W.intNeg sym x
          yneg <- W.intNeg sym y
          W.intDiv sym xneg yneg
    Nothing ->
       do xneg <- W.intNeg sym x
          yneg <- W.intNeg sym y
          zneg <- W.intDiv sym xneg yneg
          z    <- W.intDiv sym x y
          W.intIte sym neg zneg z

-- NB: What4's division operation provides SMT-LIB's Euclidean division, which
-- doesn't match the round-to-neg-infinity semantics of Cryptol, so we have to
-- do some work to get the desired semantics.
intMod ::
  IsExprBuilder sym =>
  sym ->
  SymExpr sym BaseIntegerType ->
  SymExpr sym BaseIntegerType ->
  IO (SymExpr sym BaseIntegerType)
intMod sym x y = do
  neg <- W.intLt sym y =<< W.intLit sym 0
  case W.asConstantPred neg of
    Just False -> W.intMod sym x y
    Just True  ->
       do xneg <- W.intNeg sym x
          yneg <- W.intNeg sym y
          W.intNeg sym =<< W.intMod sym xneg yneg
    Nothing ->
       do xneg <- W.intNeg sym x
          yneg <- W.intNeg sym y
          z    <- W.intMod sym x y
          zneg <- W.intNeg sym =<< W.intMod sym xneg yneg
          W.intIte sym neg zneg z

------------------------------------------------------------
-- Integers mod n

toIntModOp :: SPrim sym
toIntModOp =
  Prims.natFun $ \n ->
  Prims.intFun $ \x ->
    Prims.PrimValue (VIntMod n x)

fromIntModOp :: IsExprBuilder sym => sym -> SPrim sym
fromIntModOp sym =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
    Prims.Prim (VInt <$> (W.intMod sym x =<< W.intLit sym (toInteger n)))

intModEqOp :: IsExprBuilder sym => sym -> SPrim sym
intModEqOp sym =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y -> Prims.Prim $
  do modulus <- W.intLit sym (toInteger n)
     d <- W.intSub sym x y
     r <- W.intMod sym d modulus
     z <- W.intLit sym 0
     VBool <$> W.intEq sym r z

intModBinOp ::
  IsExprBuilder sym => sym ->
  (sym -> SInt sym -> SInt sym -> IO (SInt sym)) -> SPrim sym
intModBinOp sym f =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
  Prims.intModFun $ \y -> Prims.Prim
    (VIntMod n <$> (normalizeIntMod sym n =<< f sym x y))

intModUnOp ::
  IsExprBuilder sym => sym ->
  (sym -> SInt sym -> IO (SInt sym)) -> SPrim sym
intModUnOp sym f =
  Prims.natFun $ \n ->
  Prims.intModFun $ \x ->
    Prims.Prim (VIntMod n <$> (normalizeIntMod sym n =<< f sym x))

normalizeIntMod :: IsExprBuilder sym => sym -> Natural -> SInt sym -> IO (SInt sym)
normalizeIntMod sym n x =
  case W.asInteger x of
    Nothing -> return x
    Just i -> W.intLit sym (i `mod` toInteger n)

------------------------------------------------------------
-- Stream operations

-- MkStream :: (a :: sort 0) -> (Nat -> a) -> Stream a;
mkStreamOp :: SPrim sym
mkStreamOp =
  Prims.constFun $
  Prims.strictFun $ \f -> Prims.Prim $
    do r <- newIORef Map.empty
       return $ VExtra (SStream (\n -> apply f (ready (VNat n))) r)

-- streamGet :: (a :: sort 0) -> Stream a -> Nat -> a;
streamGetOp :: forall sym. Sym sym => sym -> SPrim sym
streamGetOp sym =
  Prims.tvalFun   $ \tp ->
  Prims.strictFun $ \xs ->
  Prims.strictFun $ \ix ->
  Prims.Prim $
    case ix of
      VNat n -> lookupSStream xs n
      VBVToNat _ w ->
        do ilv <- toWord sym w
           selectV sym (lazyMux @sym (muxBVal sym tp)) ((2 ^ SW.bvWidth ilv) - 1) (lookupSStream xs) ilv
      v -> panic "streamGetOp" ["Expected Nat value, found: " <> Text.pack (show v)]

lookupSStream :: SValue sym -> Natural -> IO (SValue sym)
lookupSStream (VExtra (SStream f r)) n = do
   m <- readIORef r
   case Map.lookup n m of
     Just v  -> return v
     Nothing -> do v <- f n
                   writeIORef r (Map.insert n v m)
                   return v
lookupSStream _ _ = fail "SAWCoreWhat4.What4.lookupSStream: expected Stream"


muxBVal :: forall sym. Sym sym =>
  sym -> TValue (What4 sym) -> SBool sym -> SValue sym -> SValue sym -> IO (SValue sym)
muxBVal sym = Prims.muxValue (prims sym)

muxWhat4Extra :: forall sym. Sym sym =>
  sym -> TValue (What4 sym) -> SBool sym -> What4Extra sym -> What4Extra sym -> IO (What4Extra sym)
muxWhat4Extra sym (VDataType (ecName -> ModuleIdentifier "Prelude.Stream") [TValue tp] [] ) c x y =
  do let f i = do xi <- lookupSStream (VExtra x) i
                  yi <- lookupSStream (VExtra y) i
                  muxBVal sym tp c xi yi
     r <- newIORef Map.empty
     return (SStream f r)
muxWhat4Extra _ tp _ _ _ =
     panic "muxWhat4Extra" ["Type mismatch: " <> Text.pack (show tp)]


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

-- @selectV sym merger maxValue valueFn vx@ treats @vx@ as an index, represented
-- as a big-endian list of bits. It does a binary lookup, using @merger@ as an
-- if-then-else operator. If the index is greater than @maxValue@, then it
-- returns @valueFn maxValue@.
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
      -- NB: `i` counts down in each iteration, so we use bvAtLE (a
      -- little-endian indexing function) to ensure that the bits are processed
      -- in big-endian order. Alternatively, we could have `i` count up and use
      -- bvAtBE (a big-endian indexing function), but we use bvAtLE as it is
      -- slightly cheaper to compute.
      p <- SW.bvAtLE sym vx (toInteger j)
      merger p (impl j (y `setBit` j)) (impl j y) where j = i - 1

instance Show (SArray sym) where
  show (SArray arr) = show $ W.printSymExpr arr

arrayConstant ::
  W.IsSymExprBuilder sym =>
  sym ->
  TValue (What4 sym) ->
  TValue (What4 sym) ->
  SValue sym ->
  IO (SArray sym)
arrayConstant sym ity _elTy elm
  | Just (Some idx_repr) <- valueAsBaseType ity
  , Just (Some elm_expr) <- valueToSymExpr elm =
    SArray <$> W.constantArray sym (Ctx.Empty Ctx.:> idx_repr) elm_expr
  | otherwise =
    panic "arrayConstant" [
        "Argument type mismatch",
        "Index type: " <> Text.pack (show ity),
        "Element: " <> Text.pack (show elm)
    ]

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
    case symExprToValue elm_repr elm_expr of
      Just v -> return v
      Nothing ->
          panic "arrayLookup" [
             "Returned element has the wrong type",
             "Type: " <> Text.pack (show elm_repr),
             "Value: " <> Text.pack (show $ W.printSymExpr elm_expr)
          ]
  | otherwise =
      panic "arrayLookup" [
          "Invalid arguments",
          "array: " <> Text.pack (show arr),
          "index: " <> Text.pack (show idx)
      ]

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
      panic "arrayUpdate" [
         "Invalid arguments",
          "array: " <> Text.pack (show arr),
          "index: " <> Text.pack (show idx),
          "element: " <> Text.pack (show elm)
      ]

arrayCopy ::
  W.IsSymExprBuilder sym =>
  sym ->
  SArray sym ->
  SWord sym ->
  SArray sym ->
  SWord sym ->
  SWord sym ->
  IO (SArray sym)
arrayCopy sym dest_arr dest_idx src_arr src_idx len
  | SArray dest_arr_expr <- dest_arr
  , DBV dest_idx_expr <- dest_idx
  , SArray src_arr_expr <- src_arr
  , DBV src_idx_expr <- src_idx
  , DBV len_expr <- len
  , W.BaseArrayRepr (Ctx.Empty Ctx.:> idx_repr) _ <- W.exprType dest_arr_expr
  , Just Refl <- testEquality (W.exprType dest_arr_expr) (W.exprType src_arr_expr)
  , Just Refl <- testEquality idx_repr (W.exprType dest_idx_expr)
  , Just Refl <- testEquality idx_repr (W.exprType src_idx_expr)
  , Just Refl <- testEquality idx_repr (W.exprType len_expr) =
    SArray <$> W.arrayCopy sym dest_arr_expr dest_idx_expr src_arr_expr src_idx_expr len_expr
  | otherwise =
      panic "arrayCopy" [
         "Invalid arguments",
          "dest array: " <> Text.pack (show dest_arr),
          "dest index: " <> Text.pack (show dest_idx),
          "src array: " <> Text.pack (show src_arr),
          "src index: " <> Text.pack (show src_idx),
          "length: " <> Text.pack (show len)
      ]

arraySet ::
  W.IsSymExprBuilder sym =>
  sym ->
  SArray sym ->
  SWord sym ->
  SValue sym ->
  SWord sym ->
  IO (SArray sym)
arraySet sym arr idx elm len
  | SArray arr_expr <- arr
  , DBV idx_expr <- idx
  , Just (Some elm_expr) <- valueToSymExpr elm
  , DBV len_expr <- len
  , W.BaseArrayRepr (Ctx.Empty Ctx.:> idx_repr) elm_repr <- W.exprType arr_expr
  , Just Refl <- testEquality idx_repr (W.exprType idx_expr)
  , Just Refl <- testEquality idx_repr (W.exprType len_expr)
  , Just Refl <- testEquality elm_repr (W.exprType elm_expr) =
    SArray <$> W.arraySet sym arr_expr idx_expr elm_expr len_expr
  | otherwise =
      panic "arraySet" [
         "Invalid arguments",
          "array: " <> Text.pack (show arr),
          "index: " <> Text.pack (show idx),
          "element: " <> Text.pack (show elm),
          "length: " <> Text.pack (show len)
      ]

arrayRangeEq ::
  W.IsSymExprBuilder sym =>
  sym ->
  SArray sym ->
  SWord sym ->
  SArray sym ->
  SWord sym ->
  SWord sym ->
  IO (SBool sym)
arrayRangeEq sym x_arr x_idx y_arr y_idx len
  | SArray x_arr_expr <- x_arr
  , DBV x_idx_expr <- x_idx
  , SArray y_arr_expr <- y_arr
  , DBV y_idx_expr <- y_idx
  , DBV len_expr <- len
  , W.BaseArrayRepr (Ctx.Empty Ctx.:> idx_repr) _ <- W.exprType x_arr_expr
  , Just Refl <- testEquality (W.exprType x_arr_expr) (W.exprType y_arr_expr)
  , Just Refl <- testEquality idx_repr (W.exprType x_idx_expr)
  , Just Refl <- testEquality idx_repr (W.exprType y_idx_expr)
  , Just Refl <- testEquality idx_repr (W.exprType len_expr) =
    W.arrayRangeEq sym x_arr_expr x_idx_expr y_arr_expr y_idx_expr len_expr
  | otherwise =
      panic "arrayRangeEq" [
          "Invalid arguments",
          "x array: " <> Text.pack (show x_arr),
          "x index: " <> Text.pack (show x_idx),
          "y array: " <> Text.pack (show y_arr),
          "y index: " <> Text.pack (show y_idx),
          "length: " <> Text.pack (show len)
      ]

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
      panic "arrayEq" [
         "Invalid arguments",
          "LHS array: " <> Text.pack (show lhs_arr),
          "RHS array: " <> Text.pack (show rhs_arr)
      ]

arrayIte ::
  W.IsSymExprBuilder sym =>
  sym ->
  W.Pred sym ->
  SArray sym ->
  SArray sym ->
  IO (SArray sym)
arrayIte sym cond lhs_arr rhs_arr
  | SArray lhs_arr_expr <- lhs_arr
  , SArray rhs_arr_expr <- rhs_arr
  , W.BaseArrayRepr (Ctx.Empty Ctx.:> lhs_idx_repr) lhs_elm_repr <- W.exprType lhs_arr_expr
  , W.BaseArrayRepr (Ctx.Empty Ctx.:> rhs_idx_repr) rhs_elm_repr <- W.exprType rhs_arr_expr
  , Just Refl <- testEquality lhs_idx_repr rhs_idx_repr
  , Just Refl <- testEquality lhs_elm_repr rhs_elm_repr =
    SArray <$> W.arrayIte sym cond lhs_arr_expr rhs_arr_expr
  | otherwise =
      panic "arrayIte" [
          "Invalid arguments",
          "Condition: " <> Text.pack (show $ W.printSymExpr cond),
          "LHS array: " <> Text.pack (show lhs_arr),
          "RHS array: " <> Text.pack (show rhs_arr)
      ]

----------------------------------------------------------------------
-- | A basic symbolic simulator/evaluator: interprets a saw-core Term as
-- a symbolic value

w4SolveBasic ::
  forall sym. IsSymExprBuilder sym =>
  sym ->
  SharedContext ->
  Map Ident (SPrim sym) {- ^ additional primitives -} ->
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
     let neutral _ nt = fail ("w4SolveBasic: could not evaluate neutral term: " ++ show nt)
     let primHandler = Sim.defaultPrimHandler
     cfg <- Sim.evalGlobal m (constMap sym `Map.union` addlPrims) extcns uninterpreted neutral primHandler
     Sim.evalSharedTerm cfg t


----------------------------------------------------------------------
-- Uninterpreted function cache

{-
data SymFnWrapper sym :: Ctx.Ctx BaseType -> Type where
  SymFnWrapper :: !(W.SymFn sym args ret) -> SymFnWrapper sym (args Ctx.::> ret)
-}
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
    VPiType nm _ body
      -> pure $ VFun nm $ \x ->
           do x' <- force x
              app' <- applyUnintApp sym app x'
              t2 <- applyPiBody body (ready x')
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
    VCtorApp i ps xv          -> foldM (applyUnintApp sym) app' =<< traverse force (ps++xv)
                                   where app' = suffixUnintApp ("_" ++ (Text.unpack (toShortName (ecName i)))) app0
    VNat n                    -> return (suffixUnintApp ("_" ++ show n) app0)
    VBVToNat w v'             -> applyUnintApp sym app' v'
                                   where app' = suffixUnintApp ("_" ++ show w) app0
    TValue (suffixTValue -> Just s)
                              -> return (suffixUnintApp s app0)
    VFun _ _ ->
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
  IO ([(ExtCns Term, (Labeler sym, SValue sym))], [SBool sym])
w4Solve sym sc satq =
  do let varList  = Map.toList (satVariables satq)
     vars <- evalStateT (traverse (traverse (newVarFOT sym)) varList) 0
     let varMap   = Map.fromList [ (ecVarIndex ec, v) | (ec, (_,v)) <- vars ]
     ref <- newIORef Map.empty

     bvals <- mapM (w4SolveAssert sym sc varMap ref (satUninterp satq)) (satAsserts satq)
     return (vars, bvals)


w4SolveAssert :: forall sym.
  IsSymExprBuilder sym =>
  sym ->
  SharedContext ->
  Map VarIndex (SValue sym) {- ^ bindings for ExtCns values -} ->
  IORef (SymFnCache sym) {- ^ cache for uninterpreted function symbols -} ->
  Set VarIndex {- ^ variables to hold uninterpreted -} ->
  SATAssert ->
  IO (SBool sym)
w4SolveAssert sym sc varMap ref uninterp (BoolAssert x) =
  do bval <- w4SolveBasic sym sc mempty varMap ref uninterp x
     case bval of
       VBool v -> return v
       _ -> fail $ "w4SolveAssert: non-boolean result type. " ++ show bval

w4SolveAssert sym sc varMap ref uninterp (UniversalAssert vars hyps concl) =
  do g <- case hyps of
            [] -> return concl
            _  -> do h <- scAndList sc hyps
                     scImplies sc h concl
     (svals,bndvars) <- boundFOTs sym vars
     let varMap' = foldl (\m ((ec,_fot), sval) -> Map.insert (ecVarIndex ec) sval m)
                         varMap
                         (zip vars svals) -- NB, boundFOTs will construct these lists to be the same length
     bval <- w4SolveBasic sym sc mempty varMap' ref uninterp g
     case bval of
       VBool v ->
         do final <- foldM (\p (Some bndvar) -> W.forallPred sym bndvar p) v bndvars
            return final

       _ -> fail $ "w4SolveAssert: non-boolean result type. " ++ show bval

-- | Given a list of external constants with first-order types,
--   descend in to the structure of those types (as needed) and construct
--   corresponding What4 bound variables so we can bind them using
--   a forall quantifier. At the same time construct @SValue@s containing
--   those variables suitable for passing to the term evaluator as substituions
--   for the given @ExtCns@ values. The length of the @SValue@ list returned
--   will match the list of the input @ExtCns@ list, but the list of What4
--   @BoundVar@s might not.
--
--   This procedure it capable of handling most first-order types, execpt
--   that Array types must have base types as index and result types rather
--   than more general first-order types. (TODO? should we actually restrict the
--   @FirstOrderType@ in the same way?)
boundFOTs :: forall sym.
  IsSymExprBuilder sym =>
  sym ->
  [(ExtCns Term, FirstOrderType)] ->
  IO ([SValue sym], [Some (BoundVar sym)])
boundFOTs sym vars =
  do (svals,(bndvars,_)) <- runStateT (mapM (uncurry handleVar) vars) ([], 0)
     return (svals, bndvars)

 where
   freshBnd :: ExtCns Term -> W.BaseTypeRepr tp -> StateT ([Some (BoundVar sym)],Integer) IO (SymExpr sym tp)
   freshBnd ec tpr =
     do (vs,n) <- get
        let nm = Text.unpack (toShortName (ecName ec)) ++ "." ++ show n
        bvar <- lift (W.freshBoundVar sym (W.safeSymbol nm) tpr)
        put (Some bvar : vs, n+1)
        return (W.varExpr sym bvar)

   handleVar :: ExtCns Term -> FirstOrderType -> StateT ([Some (BoundVar sym)], Integer) IO (SValue sym)
   handleVar ec fot =
     case fot of
       FOTBit -> VBool <$> freshBnd ec BaseBoolRepr
       FOTInt -> VInt  <$> freshBnd ec BaseIntegerRepr
       FOTIntMod m -> VIntMod m <$> freshBnd ec BaseIntegerRepr

       FOTVec n FOTBit ->
         case somePosNat n of
           Nothing -> -- n == 0
             return (VWord ZBV)
           Just (Some (PosNat nr)) ->
             VWord . DBV <$> freshBnd ec (BaseBVRepr nr)

       FOTVec n tp -> -- NB, not Bit
         do vs  <- V.replicateM (fromIntegral n) (handleVar ec tp)
            vs' <- traverse (return . ready) vs
            return (VVector vs')

       FOTRec tm ->
         do vs  <- traverse (handleVar ec) tm
            vs' <- traverse (return . ready) vs
            return (vRecord vs')

       FOTTuple ts ->
         do vs  <- traverse (handleVar ec) ts
            vs' <- traverse (return . ready) vs
            return (vTuple vs')

       FOTArray idx res
         | Just (Some idx_repr) <- fotToBaseType idx
         , Just (Some res_repr) <- fotToBaseType res

         -> VArray . SArray <$> freshBnd ec (BaseArrayRepr (Ctx.Empty Ctx.:> idx_repr) res_repr)

         | otherwise -> fail ("boundFOTs: cannot handle " ++ show fot)


--
-- Pull out argument types until bottoming out at a non-Pi type
--
argTypes :: IsSymExprBuilder sym => Value (What4 sym) -> IO [TValue (What4 sym)]
argTypes v =
   case v of
     TValue t -> loop t
     _ -> panic "argTypes" ["Expected type value: " <> Text.pack (show v)]

  where
    loop (VPiType _nm v1 body) =
      do x  <- delay (fail "argTypes: unsupported dependent SAW-Core type")
         v2 <- applyPiBody body x
         vs <- loop v2
         return (v1 : vs)

    loop _ = return []

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
  | VecLabel
      FirstOrderType
      -- ^ The element type. It is necessary to store this in case the Vec is
      -- empty, in which case we cannot retrieve the type from the element
      -- values.
      (Vector (Labeler sym))
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
       return (VecLabel tp labels, VVector args)

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
    VecLabel vty labels ->
      FOVVec vty <$> traverse (getLabelValues f) (V.toList labels)
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
-- of what4. The term may have any first-order monomorphic function
-- type. Return a term with the same type.
w4EvalTerm ::
  forall n st fs.
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  SharedContext ->
  Map Ident (SPrim (B.ExprBuilder n st fs)) ->
  Set VarIndex ->
  Term ->
  IO Term
w4EvalTerm sym st sc ps unintSet t =
  do modmap <- scGetModuleMap sc
     ref <- newIORef Map.empty
     let eval = w4EvalBasic sym st sc modmap ps mempty ref unintSet
     ty <- eval =<< scTypeOf sc t
     -- evaluate term to an SValue
     val <- eval t
     tytval <- toTValue ty
     -- convert SValue back into a Term
     rebuildTerm sym st sc tytval val
  where
    toTValue :: Value l -> IO (TValue l)
    toTValue (TValue x) = pure x
    toTValue _ = fail "toTValue"

rebuildTerm ::
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  SharedContext ->
  TValue (What4 (B.ExprBuilder n st fs)) ->
  SValue (B.ExprBuilder n st fs) ->
  IO Term
rebuildTerm sym st sc tv sv =
  let chokeOn what =
        -- XXX: alas, for the time being it looks like all we have for
        -- printing SValue/Value is a show instance
        fail ("saw-core-what4: rebuildTerm: cannot handle " ++ what ++ ": " ++
              show sv)
  in
  case sv of
    VFun _ _ ->
      chokeOn "lambdas (VFun)"
    VUnit ->
      scUnitValue sc
    VPair x y ->
      case tv of
        VPairType tx ty ->
          do vx <- force x
             vy <- force y
             x' <- rebuildTerm sym st sc tx vx
             y' <- rebuildTerm sym st sc ty vy
             scPairValue sc x' y'
        _ -> panic "rebuildTerm" [
                 "Pair wasn't a pair: found " <> Text.pack (show tv)
             ]
    VCtorApp _ _ _ ->
      chokeOn "constructors (VCtorApp)"
    VVector xs ->
      case tv of
        VVecType _ tx ->
          do vs <- traverse force (V.toList xs)
             xs' <- traverse (rebuildTerm sym st sc tx) vs
             tx' <- termOfTValue sc tx
             scVectorReduced sc tx' xs'
        _ -> panic "rebuildTerm" [
                 "Vector wasn't a vector: found " <> Text.pack (show tv)
             ]
    VBool x ->
      toSC sym st x
    VWord x ->
      case x of
        DBV w -> toSC sym st w
        ZBV ->
          do z <- scNat sc 0
             scBvNat sc z z
    VBVToNat _ _ ->
      chokeOn "VBVToNat"
    VIntToNat _ ->
      chokeOn "VIntToNat"
    VNat n ->
      scNat sc n
    VInt x ->
      toSC sym st x
    VIntMod _ _ ->
      chokeOn "VIntMod"
    VArray _ ->
      chokeOn "arrays (VArray)"
    VString s ->
      scString sc s
    VRecordValue _ ->
      chokeOn "records (VRecordValue)"
    VRecursor _ _ _ _ _ ->
      chokeOn "recursors (VRecursor)"
    VExtra _ ->
      chokeOn "VExtra"
    TValue _tval ->
      chokeOn "types (TValue)"


-- | Simplify a saw-core term by evaluating it through the saw backend
-- of what4.
w4EvalAny ::
  forall n st fs.
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  SharedContext ->
  Map Ident (SPrim (B.ExprBuilder n st fs)) ->
  Set VarIndex ->
  Term ->
  IO ([String],
      [SValue (B.ExprBuilder n st fs)],
      [Maybe (Labeler (B.ExprBuilder n st fs))],
      SValue (B.ExprBuilder n st fs))
w4EvalAny sym st sc ps unintSet t =
  do modmap <- scGetModuleMap sc
     ref <- newIORef Map.empty
     let eval = w4EvalBasic sym st sc modmap ps mempty ref unintSet
     ty <- eval =<< scTypeOf sc t

     -- get the names of the arguments to the function
     let lamNames = map (Text.unpack . fst) (fst (R.asLambdaList t))
     let varNames = [ "var" ++ show (i :: Integer) | i <- [0 ..] ]
     let argNames = zipWith (++) varNames (map ("_" ++) lamNames ++ repeat "")

     -- and their types
     argTs <- argTypes ty

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

     return (argNames, vars, bvs, bval')

w4Eval ::
  forall n st fs.
  B.ExprBuilder n st fs ->
  SAWCoreState n ->
  SharedContext ->
  Map Ident (SPrim (B.ExprBuilder n st fs)) ->
  Set VarIndex ->
  Term ->
  IO ([String], ([Maybe (Labeler (B.ExprBuilder n st fs))], SBool (B.ExprBuilder n st fs)))
w4Eval sym st sc ps uintSet t =
  do (argNames, _, bvs, bval) <- w4EvalAny sym st sc ps uintSet t
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
  Map Ident (SPrim (B.ExprBuilder n st fs)) {- ^ additional primitives -} ->
  Map VarIndex (SValue (B.ExprBuilder n st fs)) {- ^ bindings for ExtCns values -} ->
  IORef (SymFnCache (B.ExprBuilder n st fs)) {- ^ cache for uninterpreted function symbols -} ->
  Set VarIndex {- ^ 'unints' Constants in this list are kept uninterpreted -} ->
  Term {- ^ term to simulate -} ->
  IO (SValue (B.ExprBuilder n st fs))
w4EvalBasic sym st sc m addlPrims ecCons ref unintSet t =
  do let extcns tf (EC ix nm ty)
           | Just v <- Map.lookup ix ecCons = pure v
           | otherwise =
           do trm <- ArgTermConst <$> scTermF sc tf
              parseUninterpretedSAW sym st sc ref trm
                 (mkUnintApp (Text.unpack (toShortName nm) ++ "_" ++ show ix)) ty
     let uninterpreted tf ec
           | Set.member (ecVarIndex ec) unintSet = Just (extcns tf ec)
           | otherwise                           = Nothing
     let neutral _env nt = fail ("w4EvalBasic: could not evaluate neutral term: " ++ show nt)
     let primHandler = Sim.defaultPrimHandler
     cfg <- Sim.evalGlobal' m (constMap sym `Map.union` addlPrims) extcns uninterpreted neutral primHandler
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
  Map Ident (SPrim (B.ExprBuilder n st fs)) {- ^ additional primitives -} ->
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
     let neutral _env nt = fail ("w4SimulatorEval: could not evaluate neutral term: " ++ show nt)
     let primHandler = Sim.defaultPrimHandler
     res <- X.try $ do
              cfg <- Sim.evalGlobal' m (constMap sym `Map.union` addlPrims) extcns uninterpreted neutral primHandler
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
    VPiType nm t1 body
      -> pure $ VFun nm $ \x ->
           do x' <- force x
              app' <- applyUnintApp sym app x'
              arg <- mkArgTerm sc t1 x'
              let trm' = ArgTermApply trm arg
              t2 <- applyPiBody body (ready x')
              parseUninterpretedSAW sym st sc ref trm' app' t2

    VBoolType
      -> VBool <$> mkUninterpretedSAW sym st sc ref trm app BaseBoolRepr

    VIntType
      -> VInt  <$> mkUninterpretedSAW sym st sc ref trm app BaseIntegerRepr

    VIntModType n
      -> VIntMod n <$> mkUninterpretedSAW sym st sc ref (ArgTermFromIntMod n trm) app BaseIntegerRepr

    -- 0 width bitvector is a constant
    VVecType 0 VBoolType
      -> return $ VWord ZBV

    VVecType n VBoolType
      | Just (Some (PosNat w)) <- somePosNat n
      -> (VWord . DBV) <$> mkUninterpretedSAW sym st sc ref trm app (BaseBVRepr w)

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
          mkUninterpretedSAW sym st sc ref trm app (BaseArrayRepr (Ctx.Empty Ctx.:> idx_repr) elm_repr)

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
  SharedContext ->
  IORef (SymFnCache (B.ExprBuilder n st fs)) ->
  ArgTerm ->
  UnintApp (SymExpr (B.ExprBuilder n st fs)) ->
  BaseTypeRepr t ->
  IO (SymExpr (B.ExprBuilder n st fs) t)
mkUninterpretedSAW sym st sc ref trm (UnintApp nm args tys) ret
  | Just Refl <- testEquality Ctx.empty tys =
    bindSAWTerm sym st ret =<< reconstructArgTerm trm sc []
  | otherwise =
  do fn <- mkSymFn sym ref nm tys ret
     sawRegisterSymFunInterp st fn (reconstructArgTerm trm)
     W.applySymFn sym fn args

-- | An 'ArgTerm' is a description of how to reassemble a saw-core
-- term from a list of the atomic components it is composed of.
data ArgTerm
  = ArgTermVar
  | ArgTermBVZero -- ^ scBvNat 0 0
  | ArgTermToIntMod Natural ArgTerm -- ^ toIntMod n x
  | ArgTermFromIntMod Natural ArgTerm -- ^ fromIntMod n x
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
  | ArgTermBVToNat Natural ArgTerm

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
        ArgTermToIntMod n at1 ->
          do n' <- scNat sc n
             (x1, ts1) <- parse at1 ts0
             x <- scToIntMod sc n' x1
             pure (x, ts1)
        ArgTermFromIntMod n at1 ->
          do n' <- scNat sc n
             (x1, ts1) <- parse at1 ts0
             x <- scFromIntMod sc n' x1
             pure (x, ts1)
        ArgTermVector ty ats ->
          do (xs, ts1) <- parseList ats ts0
             x <- scVectorReduced sc ty xs
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
        ArgTermBVToNat w at1 ->
          do (x1, ts1) <- parse at1 ts0
             x <- scBvToNat sc w x1
             pure (x, ts1)

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
    (_, VArray{})        -> return ArgTermVar
    (VUnitType, VUnit)   -> return ArgTermUnit
    (VIntModType n, VIntMod _ _) -> pure (ArgTermToIntMod n ArgTermVar)

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

    (_, VCtorApp i ps vv) ->
      do mm <- scGetModuleMap sc
         ctor <-
           case lookupVarIndexInMap (ecVarIndex i) mm of
             Just (ResolvedCtor ctor) -> pure ctor
             _ -> panic "mkArgTerm" ["Constructor not found: " <> toAbsoluteName (ecName i)]
         ps' <- traverse (termOfSValue sc <=< force) ps
         vv' <- traverse (termOfSValue sc <=< force) vv
         x   <- scConstApply sc (ctorName ctor) (ps' ++ vv')
         return (ArgTermConst x)

    (_, TValue tval) ->
      do x <- termOfTValue sc tval
         pure (ArgTermConst x)

    (_, VNat n) ->
      do x <- scNat sc n
         pure (ArgTermConst x)

    (_, VBVToNat w v) ->
      do let w' = fromIntegral w -- FIXME: make w :: Natural to avoid fromIntegral
         x <- mkArgTerm sc (VVecType w' VBoolType) v
         pure (ArgTermBVToNat w' x)

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
