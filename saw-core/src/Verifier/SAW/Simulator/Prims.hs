{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Simulator.Prims
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.Prims
( Prim(..)
, BasePrims(..)
, constMap
  -- * primitive function constructors
, primFun
, strictFun
, constFun
, boolFun
, natFun
, intFun
, intModFun
, tvalFun
, stringFun
, wordFun
, vectorFun
, Pack
, Unpack

  -- * primitive computations
, selectV
, expByNatOp
, intToNatOp
, natToIntOp
, vRotateL
, vRotateR
, vShiftL
, vShiftR
, muxValue
, shifter
) where

import Prelude hiding (sequence, mapM)

import GHC.Stack( HasCallStack )

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad (liftM, unless, mzero)
import Control.Monad.Fix (MonadFix(mfix))
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Data.Functor
import Data.Maybe (fromMaybe)
import Data.Bitraversable
import Data.Bits
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as V
import Numeric.Natural (Natural)

import Verifier.SAW.Term.Functor (Ident, primType, primName)
import Verifier.SAW.Simulator.Value
import Verifier.SAW.Prim
import qualified Verifier.SAW.Prim as Prim

import qualified Verifier.SAW.Utils as Panic (panic)


-- | A utility type for implementing primitive functions.
--   This type allows primtives to more easily define
--   functions that expect certain kinds of arguments,
--   and allows the simulator to respond gracefully if
--   the actual arguments don't match the expected filters.
data Prim l
  = PrimFun    (Thunk l -> Prim l)
  | PrimStrict (Value l -> Prim l)
  | forall a. PrimFilterFun Text (Value l -> MaybeT (EvalM l) a) (a -> Prim l)
  | PrimExcept (ExceptT Text (EvalM l) (Value l))
  | Prim (EvalM l (Value l))
  | PrimValue (Value l)

-- | A primitive that takes a nonstrict argument
primFun :: (Thunk l -> Prim l) -> Prim l
primFun = PrimFun

-- | A primitive that takes a strict argument
strictFun :: (Value l -> Prim l) -> Prim l
strictFun = PrimStrict

-- | A primitive that ignores an argument
constFun :: Prim l -> Prim l
constFun p = PrimFun (const p)

-- | A primitive that requires a boolean argument
boolFun :: VMonad l => (VBool l -> Prim l) -> Prim l
boolFun = PrimFilterFun "expected Bool" r
  where r (VBool b) = pure b
        r _ = mzero

-- | A primitive that requires a concrete natural argument
natFun :: VMonad l => (Natural -> Prim l) -> Prim l
natFun = PrimFilterFun "expected Nat" r
  where r (VNat n) = pure n
        r (VCtorApp (primName -> "Prelude.Zero") [] [])  = pure 0
        r (VCtorApp (primName -> "Prelude.Succ") [] [x]) = succ <$> (r =<< lift (force x))
        r _ = mzero

-- | A primitive that requires an integer argument
intFun :: VMonad l => (VInt l -> Prim l) -> Prim l
intFun = PrimFilterFun "expected Integer" r
  where r (VInt i) = pure i
        r _ = mzero

-- | A primitive that requires a (Z n) argument
intModFun :: VMonad l => (VInt l -> Prim l) -> Prim l
intModFun = PrimFilterFun "expected IntMod" r
  where r (VIntMod _ i) = pure i
        r _ = mzero

-- | A primitive that requires a type argument
tvalFun :: VMonad l => (TValue l -> Prim l) -> Prim l
tvalFun = PrimFilterFun "expected type value" r
  where r (TValue tv) = pure tv
        r _ = mzero

stringFun :: VMonad l => (Text -> Prim l) -> Prim l
stringFun = PrimFilterFun "expected string value" r
  where r (VString x) = pure x
        r _ = mzero

-- | A primitive that requires a packed word argument
wordFun :: VMonad l => Pack l -> (VWord l -> Prim l) -> Prim l
wordFun pack = PrimFilterFun "expected word" r
  where r (VWord w)    = pure w
        r (VVector xs) = lift . pack =<< V.mapM (\x -> r' =<< lift (force x)) xs
        r _ = mzero

        r' (VBool b)   = pure b
        r' _ = mzero

-- | A primitive that requires a vector argument
vectorFun :: (VMonad l, Show (Extra l)) =>
  Unpack l -> (Vector (Thunk l) -> Prim l) -> Prim l
vectorFun unpack = PrimFilterFun "expected vector" r
  where r (VVector xs) = pure xs
        r (VWord w)    = fmap (ready . VBool) <$> lift (unpack w)
        r _ = mzero

------------------------------------------------------------
--

-- | A collection of implementations of primitives on base types.
-- These can be used to derive other primitives on higher types.
data BasePrims l =
  BasePrims
  { -- | This flag lets us know if we should attempt to build mux trees
    --   for vector selects, push @ite@ inside structures, etc.
    bpIsSymbolicEvaluator :: Bool

  , bpAsBool :: VBool l -> Maybe Bool
    -- Bitvectors
  , bpUnpack  :: VWord l -> EvalM l (Vector (VBool l))
  , bpPack    :: Vector (VBool l) -> MWord l
  , bpBvAt    :: VWord l -> Int -> MBool l
  , bpBvLit   :: Int -> Integer -> MWord l
  , bpBvSize  :: VWord l -> Int
  , bpBvJoin  :: VWord l -> VWord l -> MWord l
  , bpBvSlice :: Int -> Int -> VWord l -> MWord l
    -- Conditionals
  , bpMuxBool  :: VBool l -> VBool l -> VBool l -> MBool l
  , bpMuxWord  :: VBool l -> VWord l -> VWord l -> MWord l
  , bpMuxInt   :: VBool l -> VInt l -> VInt l -> MInt l
  , bpMuxArray :: VBool l -> VArray l -> VArray l -> MArray l
  , bpMuxExtra :: TValue l -> VBool l -> Extra l -> Extra l -> EvalM l (Extra l)
    -- Booleans
  , bpTrue   :: VBool l
  , bpFalse  :: VBool l
  , bpNot    :: VBool l -> MBool l
  , bpAnd    :: VBool l -> VBool l -> MBool l
  , bpOr     :: VBool l -> VBool l -> MBool l
  , bpXor    :: VBool l -> VBool l -> MBool l
  , bpBoolEq :: VBool l -> VBool l -> MBool l
    -- Bitvector logical
  , bpBvNot  :: VWord l -> MWord l
  , bpBvAnd  :: VWord l -> VWord l -> MWord l
  , bpBvOr   :: VWord l -> VWord l -> MWord l
  , bpBvXor  :: VWord l -> VWord l -> MWord l
    -- Bitvector arithmetic
  , bpBvNeg  :: VWord l -> MWord l
  , bpBvAdd  :: VWord l -> VWord l -> MWord l
  , bpBvSub  :: VWord l -> VWord l -> MWord l
  , bpBvMul  :: VWord l -> VWord l -> MWord l
  , bpBvUDiv :: VWord l -> VWord l -> MWord l
  , bpBvURem :: VWord l -> VWord l -> MWord l
  , bpBvSDiv :: VWord l -> VWord l -> MWord l
  , bpBvSRem :: VWord l -> VWord l -> MWord l
  , bpBvLg2  :: VWord l -> MWord l
    -- Bitvector comparisons
  , bpBvEq   :: VWord l -> VWord l -> MBool l
  , bpBvsle  :: VWord l -> VWord l -> MBool l
  , bpBvslt  :: VWord l -> VWord l -> MBool l
  , bpBvule  :: VWord l -> VWord l -> MBool l
  , bpBvult  :: VWord l -> VWord l -> MBool l
  , bpBvsge  :: VWord l -> VWord l -> MBool l
  , bpBvsgt  :: VWord l -> VWord l -> MBool l
  , bpBvuge  :: VWord l -> VWord l -> MBool l
  , bpBvugt  :: VWord l -> VWord l -> MBool l
    -- Bitvector shift/rotate
  , bpBvRolInt :: VWord l -> Integer -> MWord l
  , bpBvRorInt :: VWord l -> Integer -> MWord l
  , bpBvShlInt :: VBool l -> VWord l -> Integer -> MWord l
  , bpBvShrInt :: VBool l -> VWord l -> Integer -> MWord l
  , bpBvRol    :: VWord l -> VWord l -> MWord l
  , bpBvRor    :: VWord l -> VWord l -> MWord l
  , bpBvShl    :: VBool l -> VWord l -> VWord l -> MWord l
  , bpBvShr    :: VBool l -> VWord l -> VWord l -> MWord l
    -- Bitvector misc
  , bpBvPopcount           :: VWord l -> MWord l
  , bpBvCountLeadingZeros  :: VWord l -> MWord l
  , bpBvCountTrailingZeros :: VWord l -> MWord l
  , bpBvForall             :: Natural -> (VWord l -> MBool l) -> MBool l
    -- Integer operations
  , bpIntAdd :: VInt l -> VInt l -> MInt l
  , bpIntSub :: VInt l -> VInt l -> MInt l
  , bpIntMul :: VInt l -> VInt l -> MInt l
  , bpIntDiv :: VInt l -> VInt l -> MInt l
  , bpIntMod :: VInt l -> VInt l -> MInt l
  , bpIntNeg :: VInt l -> MInt l
  , bpIntAbs :: VInt l -> MInt l
  , bpIntEq :: VInt l -> VInt l -> MBool l
  , bpIntLe :: VInt l -> VInt l -> MBool l
  , bpIntLt :: VInt l -> VInt l -> MBool l
  , bpIntMin :: VInt l -> VInt l -> MInt l
  , bpIntMax :: VInt l -> VInt l -> MInt l
    -- Array operations
  , bpArrayConstant :: TValue l -> TValue l -> Value l -> MArray l
  , bpArrayLookup :: VArray l -> Value l -> MValue l
  , bpArrayUpdate :: VArray l -> Value l -> Value l -> MArray l
  , bpArrayEq :: VArray l -> VArray l -> MBool l
  , bpArrayCopy :: VArray l -> VWord l -> VArray l -> VWord l -> VWord l -> MArray l
  , bpArraySet :: VArray l -> VWord l -> Value l -> VWord l -> MArray l
  , bpArrayRangeEq :: VArray l -> VWord l -> VArray l -> VWord l -> VWord l -> MBool l
  }

bpBool :: VMonad l => BasePrims l -> Bool -> MBool l
bpBool bp True = return (bpTrue bp)
bpBool bp False = return (bpFalse bp)

-- | Given implementations of the base primitives, construct a table
-- containing implementations of all primitives.
constMap ::
  forall l.
  (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
  BasePrims l ->
  Map Ident (Prim l)
constMap bp = Map.fromList
  -- Boolean
  [ ("Prelude.Bool"  , PrimValue (TValue VBoolType))
  , ("Prelude.True"  , PrimValue (VBool (bpTrue bp)))
  , ("Prelude.False" , PrimValue (VBool (bpFalse bp)))
  , ("Prelude.not"   , boolFun (Prim . liftM VBool . bpNot bp))
  , ("Prelude.and"   , boolBinOp (bpAnd bp))
  , ("Prelude.or"    , boolBinOp (bpOr bp))
  , ("Prelude.xor"   , boolBinOp (bpXor bp))
  , ("Prelude.boolEq", boolBinOp (bpBoolEq bp))
  -- Bitwise
  , ("Prelude.bvAnd" , wordBinOp (bpPack bp) (bpBvAnd bp))
  , ("Prelude.bvOr"  , wordBinOp (bpPack bp) (bpBvOr  bp))
  , ("Prelude.bvXor" , wordBinOp (bpPack bp) (bpBvXor bp))
  , ("Prelude.bvNot" , wordUnOp  (bpPack bp) (bpBvNot bp))
  -- Arithmetic
  , ("Prelude.bvNeg" , wordUnOp  (bpPack bp) (bpBvNeg bp))
  , ("Prelude.bvAdd" , wordBinOp (bpPack bp) (bpBvAdd bp))
  , ("Prelude.bvSub" , wordBinOp (bpPack bp) (bpBvSub bp))
  , ("Prelude.bvMul" , wordBinOp (bpPack bp) (bpBvMul bp))
  , ("Prelude.bvUDiv", wordBinOp (bpPack bp) (bpBvUDiv bp))
  , ("Prelude.bvURem", wordBinOp (bpPack bp) (bpBvURem bp))
  , ("Prelude.bvSDiv", wordBinOp (bpPack bp) (bpBvSDiv bp))
  , ("Prelude.bvSRem", wordBinOp (bpPack bp) (bpBvSRem bp))
  , ("Prelude.bvLg2" , wordUnOp  (bpPack bp) (bpBvLg2  bp))
  -- Comparisons
  , ("Prelude.bvEq"  , wordBinRel (bpPack bp) (bpBvEq  bp))
  , ("Prelude.bvsle" , wordBinRel (bpPack bp) (bpBvsle bp))
  , ("Prelude.bvslt" , wordBinRel (bpPack bp) (bpBvslt bp))
  , ("Prelude.bvule" , wordBinRel (bpPack bp) (bpBvule bp))
  , ("Prelude.bvult" , wordBinRel (bpPack bp) (bpBvult bp))
  , ("Prelude.bvsge" , wordBinRel (bpPack bp) (bpBvsge bp))
  , ("Prelude.bvsgt" , wordBinRel (bpPack bp) (bpBvsgt bp))
  , ("Prelude.bvuge" , wordBinRel (bpPack bp) (bpBvuge bp))
  , ("Prelude.bvugt" , wordBinRel (bpPack bp) (bpBvugt bp))
    -- Bitvector misc
  , ("Prelude.bvPopcount", wordUnOp (bpPack bp) (bpBvPopcount bp))
  , ("Prelude.bvCountLeadingZeros", wordUnOp (bpPack bp) (bpBvCountLeadingZeros bp))
  , ("Prelude.bvCountTrailingZeros", wordUnOp (bpPack bp) (bpBvCountTrailingZeros bp))
  , ("Prelude.bvForall",
        natFun $ \n ->
        strictFun $ \f ->
          Prim (VBool <$>  bpBvForall bp n (toWordPred f))
    )

  -- Nat
  , ("Prelude.Succ", succOp bp)
  , ("Prelude.addNat", addNatOp bp)
  , ("Prelude.subNat", subNatOp bp)
  , ("Prelude.mulNat", mulNatOp bp)
  , ("Prelude.minNat", minNatOp bp)
  , ("Prelude.maxNat", maxNatOp bp)
  , ("Prelude.divModNat", divModNatOp bp)
  , ("Prelude.expNat", expNatOp)
  , ("Prelude.widthNat", widthNatOp)
  , ("Prelude.natCase", natCaseOp)
  , ("Prelude.equalNat", equalNatOp bp)
  , ("Prelude.ltNat", ltNatOp bp)
  -- Integers
  , ("Prelude.Integer", PrimValue (TValue VIntType))
  , ("Prelude.intAdd", intBinOp (bpIntAdd bp))
  , ("Prelude.intSub", intBinOp (bpIntSub bp))
  , ("Prelude.intMul", intBinOp (bpIntMul bp))
  , ("Prelude.intDiv", intBinOp (bpIntDiv bp))
  , ("Prelude.intMod", intBinOp (bpIntMod bp))
  , ("Prelude.intNeg", intUnOp  (bpIntNeg bp))
  , ("Prelude.intAbs", intUnOp  (bpIntAbs bp))
  , ("Prelude.intEq" , intBinCmp (bpIntEq bp))
  , ("Prelude.intLe" , intBinCmp (bpIntLe bp))
  , ("Prelude.intLt" , intBinCmp (bpIntLt bp))
  , ("Prelude.intMin", intBinOp (bpIntMin bp))
  , ("Prelude.intMax", intBinOp (bpIntMax bp))
  -- Modular Integers
  , ("Prelude.IntMod", natFun $ \n -> PrimValue (TValue (VIntModType n)))
  -- Vectors
  , ("Prelude.Vec", vecTypeOp)
  , ("Prelude.gen", genOp)
  , ("Prelude.atWithDefault", atWithDefaultOp bp)
  , ("Prelude.upd", updOp bp)
  , ("Prelude.take", takeOp bp)
  , ("Prelude.drop", dropOp bp)
  , ("Prelude.append", appendOp bp)
  , ("Prelude.join", joinOp bp)
  , ("Prelude.split", splitOp bp)
  , ("Prelude.zip", vZipOp (bpUnpack bp))
  , ("Prelude.foldr", foldrOp (bpUnpack bp))
  , ("Prelude.foldl", foldlOp (bpUnpack bp))
  , ("Prelude.scanl", scanlOp (bpUnpack bp))
  , ("Prelude.rotateL", rotateLOp bp)
  , ("Prelude.rotateR", rotateROp bp)
  , ("Prelude.shiftL", shiftLOp bp)
  , ("Prelude.shiftR", shiftROp bp)
  , ("Prelude.EmptyVec", emptyVec)
  -- Miscellaneous
  , ("Prelude.coerce", coerceOp)
  , ("Prelude.bvNat", bvNatOp bp)
  , ("Prelude.bvToNat", bvToNatOp)
  , ("Prelude.fix", fixOp)
  , ("Prelude.error", errorOp)

  -- Strings
  , ("Prelude.String", PrimValue (TValue VStringType))
  , ("Prelude.equalString", equalStringOp bp)

  -- Overloaded
  , ("Prelude.ite", iteOp bp)
  , ("Prelude.iteDep", iteDepOp bp)
  -- SMT Arrays
  , ("Prelude.Array", arrayTypeOp)
  , ("Prelude.arrayConstant", arrayConstantOp bp)
  , ("Prelude.arrayLookup", arrayLookupOp bp)
  , ("Prelude.arrayUpdate", arrayUpdateOp bp)
  , ("Prelude.arrayEq", arrayEqOp bp)
  , ("Prelude.arrayCopy", arrayCopyOp bp)
  , ("Prelude.arraySet", arraySetOp bp)
  , ("Prelude.arrayRangeEq", arrayRangeEqOp bp)
  ]

-- | Call this function to indicate that a programming error has
-- occurred, e.g. a datatype invariant has been violated.
panic :: HasCallStack => String -> a
panic msg = Panic.panic "Verifier.SAW.Simulator.Prims" [msg]

------------------------------------------------------------
-- Value accessors and constructors

vNat :: Natural -> Value l
vNat n = VNat n

toBool :: Show (Extra l) => Value l -> VBool l
toBool (VBool b) = b
toBool x = panic $ unwords ["Verifier.SAW.Simulator.toBool", show x]


type Pack l   = Vector (VBool l) -> MWord l
type Unpack l = VWord l -> EvalM l (Vector (VBool l))

toWord :: (HasCallStack, VMonad l, Show (Extra l))
       => Pack l -> Value l -> MWord l
toWord _ (VWord w) = return w
toWord pack (VVector vv) = pack =<< V.mapM (liftM toBool . force) vv
toWord _ x = panic $ unwords ["Verifier.SAW.Simulator.toWord", show x]

toWordPred :: (HasCallStack, VMonad l, Show (Extra l))
           => Value l -> VWord l -> MBool l
toWordPred (VFun _ f) = fmap toBool . f . ready . VWord
toWordPred x = panic $ unwords ["Verifier.SAW.Simulator.toWordPred", show x]

toBits :: (HasCallStack, VMonad l, Show (Extra l))
       => Unpack l -> Value l -> EvalM l (Vector (VBool l))
toBits unpack (VWord w) = unpack w
toBits _ (VVector v) = V.mapM (liftM toBool . force) v
toBits _ x = panic $ unwords ["Verifier.SAW.Simulator.toBits", show x]

toVector :: (HasCallStack, VMonad l, Show (Extra l))
         => Unpack l -> Value l -> ExceptT Text (EvalM l) (Vector (Thunk l))
toVector _ (VVector v) = return v
toVector unpack (VWord w) = lift (liftM (fmap (ready . VBool)) (unpack w))
toVector _ x = throwE $ "Verifier.SAW.Simulator.toVector " <> Text.pack (show x)

vecIdx :: a -> Vector a -> Int -> a
vecIdx err v n =
  case (V.!?) v n of
    Just a -> a
    Nothing -> err

toArray :: (HasCallStack, VMonad l, Show (Extra l)) => Value l -> MArray l
toArray (VArray f) = return f
toArray x = panic $ unwords ["Verifier.SAW.Simulator.toArray", show x]

------------------------------------------------------------
-- Standard operator types

-- op :: Bool -> Bool -> Bool;
boolBinOp ::
  (VMonad l, Show (Extra l)) =>
  (VBool l -> VBool l -> MBool l) -> Prim l
boolBinOp op =
  boolFun $ \x ->
  boolFun $ \y ->
    Prim (VBool <$> op x y)

-- op : (n : Nat) -> Vec n Bool -> Vec n Bool;
wordUnOp ::
  (VMonad l, Show (Extra l)) =>
  Pack l -> (VWord l -> MWord l) -> Prim l
wordUnOp pack op =
  constFun $
  wordFun pack $ \x ->
    Prim (VWord <$> op x)

-- op : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
wordBinOp ::
  (VMonad l, Show (Extra l)) =>
  Pack l -> (VWord l -> VWord l -> MWord l) -> Prim l
wordBinOp pack op =
  constFun $
  wordFun pack $ \x ->
  wordFun pack $ \y ->
    Prim (VWord <$> op x y)

-- op : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
wordBinRel ::
  (VMonad l, Show (Extra l)) =>
  Pack l -> (VWord l -> VWord l -> MBool l) -> Prim l
wordBinRel pack op =
  constFun $
  wordFun pack $ \x ->
  wordFun pack $ \y ->
    Prim (VBool <$> op x y)

------------------------------------------------------------
-- Utility functions

-- @selectV mux maxValue valueFn v@ treats the vector @v@ as an
-- index, represented as a big-endian list of bits. It does a binary
-- lookup, using @mux@ as an if-then-else operator. If the index is
-- greater than @maxValue@, then it returns @valueFn maxValue@.
selectV :: (b -> a -> a -> a) -> Int -> (Int -> a) -> Vector b -> a
selectV mux maxValue valueFn v = impl len 0
  where
    len = V.length v
    err = panic "selectV: impossible"
    impl _ x | x > maxValue || x < 0 = valueFn maxValue
    impl 0 x = valueFn x
    impl i x = mux (vecIdx err v (len - i)) (impl j (x `setBit` j)) (impl j x) where j = i - 1

------------------------------------------------------------
-- Values for common primitives

-- bvNat : (n : Nat) -> Nat -> Vec n Bool;
bvNatOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
bvNatOp bp =
  natFun $ \w ->
  -- make sure our nat has a size, i.e. that 'natToWord' will not fail
  natSizeFun $ either snd VNat <&> \v ->
    Prim (VWord <$> natToWord bp (fromIntegral w) v) -- FIXME check for overflow on w

-- bvToNat : (n : Nat) -> Vec n Bool -> Nat;
bvToNatOp :: VMonad l => Prim l
bvToNatOp =
  natFun $ \n ->
  primFun $ \x ->
    Prim (liftM (VBVToNat (fromIntegral n)) (force x)) -- TODO, bad fromIntegral

-- coerce :: (a b :: sort 0) -> Eq (sort 0) a b -> a -> b;
coerceOp :: VMonad l => Prim l
coerceOp =
  constFun $
  constFun $
  constFun $
  primFun (\x -> Prim (force x))

------------------------------------------------------------
-- Nat primitives

-- | Return the number of bits necessary to represent the given value,
-- which should be a value of type Nat.
natSizeMaybe :: HasCallStack => Value l -> Maybe Natural
natSizeMaybe val =
  case val of
    VNat n -> Just $ widthNat n
    VBVToNat n _ -> Just $ fromIntegral n -- TODO, remove this fromIntegral
    VIntToNat _ -> panic "natSize: symbolic integer (TODO)"
    _ -> Nothing

-- | Return the number of bits necessary to represent the given value,
-- which should be a value of type Nat, calling 'panic' if this cannot be done.
natSize :: (HasCallStack, Show (Extra l)) => Value l -> Natural
natSize val = fromMaybe (panic $ "natSize: expected Nat, got: " ++ show val)
                        (natSizeMaybe val)

-- | A primitive that requires a natural argument, returning its value as a
-- 'Natural' if the argument is concrete, or a pair of a size in bits and a
-- 'Value', if 'natSizeMaybe' returns 'Just'
natSizeFun :: (HasCallStack, VMonad l) =>
              (Either (Natural, Value l) Natural -> Prim l) -> Prim l
natSizeFun = PrimFilterFun "expected Nat" r
  where r (VNat n) = pure (Right n)
        r (VCtorApp (primName -> "Prelude.Zero") [] []) = pure (Right 0)
        r v@(VCtorApp (primName -> "Prelude.Succ") [] [x]) =
          lift (force x) >>= r >>= bimapM (const (szPr v)) (pure . succ)
        r v = Left <$> szPr v
        szPr v = maybe mzero (pure . (,v)) (natSizeMaybe v)

-- | Convert the given value (which should be of type Nat) to a word
-- of the given bit-width. The bit-width must be at least as large as
-- that returned by @natSize@.
natToWord :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l ->
             Natural -> Value l -> MWord l
natToWord bp w val =
  unless (w <= fromIntegral (maxBound :: Int))
         (panic "natToWord" ["width too large", show w]) >>
  -- TODO, remove the calls to fromIntegral below
  case val of
    VNat n -> bpBvLit bp (fromIntegral w) (toInteger n)
    VIntToNat _i -> panic "natToWord of VIntToNat TODO!"
    VBVToNat xsize v ->
      do x <- toWord (bpPack bp) v
         case compare xsize (fromIntegral w) of
           GT -> bpBvSlice bp (xsize - fromIntegral w) (fromIntegral w) x
           EQ -> return x
           LT -> -- zero-extend x to width w
             do pad <- bpBvLit bp (fromIntegral w - xsize) 0
                bpBvJoin bp pad x
    _ -> panic $ "natToWord: expected Nat, got: " ++ show val

-- | A primitive which is a unary operation on a natural argument.
-- The second argument gives how to modify the size in bits of this operation's
-- argument so that no overflow occurs (e.g. 'succ' for 'succ').
-- The third argument gives this operation for a concrete natural argument.
-- The fourth argument gives this operation for a natural argument of the given
-- size in bits.
unaryNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l ->
              (Natural -> Natural) ->
              (Natural -> MValue l) ->
              (Int -> VWord l -> MValue l) -> Prim l
unaryNatOp bp fw fn fv = natSizeFun $ \case
  Right n -> Prim (fn n)
  Left (w1,v) -> Prim $ do let w = fw w1
                           x <- natToWord bp w v
                           fv (fromIntegral w) x

-- | A primitive which is a unary operation on a natural argument and which
-- returns a natural.
-- The second argument gives how to modify the size in bits of this operation's
-- argument so that no overflow occurs (e.g. 'succ' for 'succ').
-- The third argument gives this operation for a concrete natural argument.
-- The fourth argument gives this operation for a natural argument of the given
-- size in bits.
unaryNatToNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l ->
                   (Natural -> Natural) ->
                   (Natural -> Natural) ->
                   (Int -> VWord l -> MWord l) -> Prim l
unaryNatToNatOp bp fw fn fv =
  unaryNatOp bp fw (\n -> pure (vNat (fn n)))
                   (\w x -> VBVToNat w . VWord <$> fv w x)

-- | A primitive which is a binary operation on natural arguments.
-- The second argument gives how to combine the the sizes in bits of this
-- operation's arguments so that no overflow occurs (e.g. 'max' for
-- comparisons, @(\w1 w2 -> suc (max w1 w2))@ for addition, '(+)' for
-- multiplication).
-- The third argument gives this operation for concrete natural arguments.
-- The fourth argument gives this operation for natural arguments of the size
-- in bits given by the second argument.
binNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l ->
            (Natural -> Natural -> Natural) ->
            (Natural -> Natural -> MValue l) ->
            (Int -> VWord l -> VWord l -> MValue l) -> Prim l
binNatOp bp fw fn fv = natSizeFun (natSizeFun . go)
  where go (Right m) (Right n) = Prim (fn m n)
        go (Right m) (Left pr) = go (Left (widthNat m, VNat m)) (Left pr)
        go (Left pr) (Right n) = go (Left pr) (Left (widthNat n, VNat n))
        go (Left (w1,v1)) (Left (w2,v2)) = Prim $
          do let w = fw w1 w2
             x1 <- natToWord bp w v1
             x2 <- natToWord bp w v2
             fv (fromIntegral w) x1 x2

-- | A primitive which is a binary operation on natural arguments and which
-- returns a natural.
-- The second argument gives how to combine the the sizes in bits of this
-- operation's arguments so that no overflow occurs (e.g. 'max' for
-- comparisons, @(\w1 w2 -> suc (max w1 w2))@ for addition, '(+)' for
-- multiplication).
-- The third argument gives this operation for concrete natural arguments.
-- The fourth argument gives this operation for natural arguments of the size
-- in bits given by the second argument.
binNatToNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l ->
                 (Natural -> Natural -> Natural) ->
                 (Natural -> Natural -> Natural) ->
                 (Int -> VWord l -> VWord l -> MWord l) -> Prim l
binNatToNatOp bp fw fn fv =
  binNatOp bp fw (\m n -> pure (vNat (fn m n)))
                 (\w x1 x2 -> VBVToNat w . VWord <$> fv w x1 x2)

-- Succ :: Nat -> Nat;
succOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l -> Prim l
succOp bp = unaryNatToNatOp bp succ succ (\w x -> do o <- bpBvLit bp w 1
                                                     bpBvAdd bp x o)

-- addNat :: Nat -> Nat -> Nat;
addNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l -> Prim l
addNatOp bp = binNatToNatOp bp (\w1 w2 -> succ (max w1 w2))
                               (+) (\_ -> bpBvAdd bp)

-- subNat :: Nat -> Nat -> Nat;
subNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l -> Prim l
subNatOp bp = binNatToNatOp bp (\w1 w2 -> max w1 w2)
                               (\i j -> if i < j then 0 else i - j)
                               (\w x1 x2 -> do lt <- bpBvult bp x1 x2
                                               z <- bpBvLit bp w 0
                                               d <- bpBvSub bp x1 x2
                                               bpMuxWord bp lt z d)

-- mulNat :: Nat -> Nat -> Nat;
mulNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l -> Prim l
mulNatOp bp = binNatToNatOp bp (+) (*) (\_ -> bpBvMul bp)

-- minNat :: Nat -> Nat -> Nat;
minNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l -> Prim l
minNatOp bp = binNatToNatOp bp max min
                               (\_ x1 x2 -> do lt <- bpBvult bp x1 x2
                                               bpMuxWord bp lt x1 x2)

-- maxNat :: Nat -> Nat -> Nat;
maxNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l -> Prim l
maxNatOp bp = binNatToNatOp bp max max
                               (\_ x1 x2 -> do lt <- bpBvult bp x1 x2
                                               bpMuxWord bp lt x2 x1)

-- divModNat :: Nat -> Nat -> #(Nat, Nat);
divModNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l -> Prim l
divModNatOp bp = binNatOp bp max
                 (\m n -> let (q,r) = divMod m n in
                          pure $ vTuple [ready $ vNat q, ready $ vNat r])
                 (\w x1 x2 -> do q <- VBVToNat w . VWord <$> bpBvUDiv bp x1 x2
                                 r <- VBVToNat w . VWord <$> bpBvURem bp x1 x2
                                 pure $ vTuple [ready q, ready r])

-- expNat :: Nat -> Nat -> Nat;
expNatOp :: VMonad l => Prim l
expNatOp =
  natFun $ \m ->
  natFun $ \n ->
    PrimValue (vNat (m ^ n))

-- widthNat :: Nat -> Nat;
widthNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => Prim l
widthNatOp = natSizeFun $ \case
  Right n -> PrimValue (vNat (widthNat n))
  Left (w,_) -> PrimValue (vNat w)

-- equalNat :: Nat -> Nat -> Bool;
equalNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l -> Prim l
equalNatOp bp = binNatOp bp max (\i j -> VBool <$> bpBool bp (i == j))
                                (\_ x1 x2 -> VBool <$> bpBvEq bp x1 x2)

-- ltNat :: Nat -> Nat -> Bool;
ltNatOp :: (HasCallStack, VMonad l, Show (Extra l)) => BasePrims l -> Prim l
ltNatOp bp = binNatOp bp max (\i j -> VBool <$> bpBool bp (i < j))
                             (\_ x1 x2 -> VBool <$> bpBvult bp x1 x2)

-- natCase :: (p :: Nat -> sort 0) -> p Zero -> ((n :: Nat) -> p (Succ n)) -> (n :: Nat) -> p n;
natCaseOp :: (VMonad l, Show (Extra l)) => Prim l
natCaseOp =
  constFun $
  primFun $ \z ->
  primFun $ \s ->
  natFun $ \n -> Prim $
    if n == 0
    then force z
    else do s' <- force s
            apply s' (ready (VNat (n - 1)))

--------------------------------------------------------------------------------
-- Strings

equalStringOp :: VMonad l => BasePrims l -> Prim l
equalStringOp bp =
  stringFun $ \x ->
  stringFun $ \y ->
    Prim (VBool <$> bpBool bp (x == y))

--------------------------------------------------------------------------------

-- Vec :: (n :: Nat) -> (a :: sort 0) -> sort 0;
vecTypeOp :: VMonad l => Prim l
vecTypeOp =
  natFun $ \n ->
  tvalFun $ \a ->
    PrimValue (TValue (VVecType n a))

-- gen :: (n :: Nat) -> (a :: sort 0) -> (Nat -> a) -> Vec n a;
genOp :: (VMonadLazy l, Show (Extra l)) => Prim l
genOp =
  natFun $ \n ->
  constFun $
  strictFun $ \f -> Prim $
    do let g i = delay $ apply f (ready (VNat (fromIntegral i)))
       if toInteger n > toInteger (maxBound :: Int) then
         panic ("Verifier.SAW.Simulator.gen: vector size too large: " ++ show n)
         else liftM VVector $ V.generateM (fromIntegral n) g


-- atWithDefault :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> a;
atWithDefaultOp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Prim l
atWithDefaultOp bp =
  natFun $ \n ->
  tvalFun $ \tp ->
  primFun $ \d ->
  strictFun $ \x ->
  strictFun $ \idx ->
  PrimExcept $
    case idx of
      VNat i ->
        case x of
          VVector xv -> lift (force (vecIdx d xv (fromIntegral i))) -- FIXME dangerous fromIntegral
          VWord xw -> lift (VBool <$> bpBvAt bp xw (fromIntegral i)) -- FIXME dangerous fromIntegral
          _ -> throwE "atOp: expected vector"
      VBVToNat _sz i | bpIsSymbolicEvaluator bp -> do
        iv <- lift (toBits (bpUnpack bp) i)
        case x of
          VVector xv ->
            lift $ selectV (lazyMuxValue bp tp) (fromIntegral n - 1) (force . vecIdx d xv) iv -- FIXME dangerous fromIntegral
          VWord xw ->
            lift $ selectV (lazyMuxValue bp tp) (fromIntegral n - 1) (liftM VBool . bpBvAt bp xw) iv -- FIXME dangerous fromIntegral
          _ -> throwE "atOp: expected vector"

      VIntToNat _i | bpIsSymbolicEvaluator bp -> panic "atWithDefault: symbolic integer TODO"

      _ -> throwE $ "atOp: expected Nat, got " <> Text.pack (show idx)

-- upd :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a -> Vec n a;
updOp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Prim l
updOp bp =
  natFun $ \n ->
  tvalFun $ \tp ->
  vectorFun (bpUnpack bp) $ \xv ->
  strictFun $ \idx ->
  primFun $ \y ->
  PrimExcept $
    case idx of
      VNat i
        | toInteger i < toInteger (V.length xv)
           -> return (VVector (xv V.// [(fromIntegral i, y)]))
        | otherwise                   -> return (VVector xv)
      VBVToNat wsize (VWord w) | bpIsSymbolicEvaluator bp -> lift $
        do let f i = do b <- bpBvEq bp w =<< bpBvLit bp wsize (toInteger i)
                        if wsize < 64 && toInteger i >= 2 ^ wsize
                          then return (xv V.! i)
                          else delay (lazyMuxValue bp tp b (force y) (force (xv V.! i)))
           yv <- V.generateM (V.length xv) f
           return (VVector yv)
      VBVToNat _sz (VVector iv) | bpIsSymbolicEvaluator bp -> lift $
        do let update i = return (VVector (xv V.// [(i, y)]))
           iv' <- V.mapM (liftM toBool . force) iv
           selectV (lazyMuxValue bp (VVecType n tp)) (fromIntegral n - 1) update iv' -- FIXME dangerous fromIntegral

      VIntToNat _ | bpIsSymbolicEvaluator bp -> panic "updOp: symbolic integer TODO"

      _ -> throwE $ "updOp: expected Nat, got " <> Text.pack (show idx)

-- primitive EmptyVec :: (a :: sort 0) -> Vec 0 a;
emptyVec :: VMonad l => Prim l
emptyVec = constFun (PrimValue (VVector V.empty))

-- take :: (a :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) a -> Vec m a;
takeOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
takeOp bp =
  constFun $
  natFun $ \(fromIntegral -> m) ->  -- FIXME dangerous fromIntegral
  constFun $
  strictFun $ \v ->
  PrimExcept $
    case v of
      VVector vv -> return (VVector (V.take m vv))
      VWord vw -> lift (VWord <$> bpBvSlice bp 0 m vw)
      _ -> throwE $ "takeOp: " <> Text.pack (show v)

-- drop :: (a :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) a -> Vec n a;
dropOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
dropOp bp =
  constFun $
  natFun $ \(fromIntegral -> m) -> -- FIXME dangerous fromIntegral
  constFun $
  strictFun $ \v ->
  PrimExcept $
  case v of
    VVector vv -> return (VVector (V.drop m vv))
    VWord vw -> lift (VWord <$> bpBvSlice bp m (bpBvSize bp vw - m) vw)
    _ -> throwE $ "dropOp: " <> Text.pack (show v)

-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
appendOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
appendOp bp =
  constFun $
  constFun $
  constFun $
  strictFun $ \xs ->
  strictFun $ \ys ->
  PrimExcept (appV bp xs ys)

appV :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l -> Value l -> ExceptT Text (EvalM l) (Value l)
appV bp xs ys =
  case (xs, ys) of
    (VVector xv, _) | V.null xv -> return ys
    (_, VVector yv) | V.null yv -> return xs
    (VWord xw, VWord yw) -> lift (VWord <$> bpBvJoin bp xw yw)
    (VVector xv, VVector yv) -> return $ VVector ((V.++) xv yv)
    (VVector xv, VWord yw) -> lift (liftM (\yv -> VVector ((V.++) xv (fmap (ready . VBool) yv))) (bpUnpack bp yw))
    (VWord xw, VVector yv) -> lift (liftM (\xv -> VVector ((V.++) (fmap (ready . VBool) xv) yv)) (bpUnpack bp xw))
    _ -> throwE $ "Verifier.SAW.Simulator.Prims.appendOp: " <> Text.pack (show xs) <> ", " <> Text.pack (show ys)

-- join  :: (m n :: Nat) -> (a :: sort 0) -> Vec m (Vec n a) -> Vec (mulNat m n) a;
joinOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
joinOp bp =
  constFun $
  constFun $
  constFun $
  strictFun $ \x ->
  PrimExcept $
  case x of
    VVector xv -> do
      vv <- lift (V.mapM force xv)
      V.foldM (appV bp) (VVector V.empty) vv
    _ -> throwE "Verifier.SAW.Simulator.Prims.joinOp"

-- split :: (m n :: Nat) -> (a :: sort 0) -> Vec (mulNat m n) a -> Vec m (Vec n a);
splitOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
splitOp bp =
  natFun $ \(fromIntegral -> m) ->  -- FIXME dangerous fromIntegral
  natFun $ \(fromIntegral -> n) ->  -- FIXME dangerous fromIntegral
  constFun $
  strictFun $ \x ->
  PrimExcept $
  case x of
    VVector xv ->
      let f i = ready (VVector (V.slice (i*n) n xv))
      in return (VVector (V.generate m f))
    VWord xw ->
      let f i = (ready . VWord) <$> bpBvSlice bp (i*n) n xw
      in lift (VVector <$> V.generateM m f)
    _ -> throwE "Verifier.SAW.Simulator.SBV.splitOp"

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: (VMonadLazy l, Show (Extra l)) => Unpack l -> Prim l
vZipOp unpack =
  constFun $
  constFun $
  constFun $
  constFun $
  strictFun $ \x ->
  strictFun $ \y ->
  PrimExcept $
  do xv <- toVector unpack x
     yv <- toVector unpack y
     let pair a b = ready (vTuple [a, b])
     return (VVector (V.zipWith pair xv yv))


--------------------------------------------------------------------------
-- Generic square-and-multiply

-- primitive expByNat : (a:sort 0) -> a -> (a -> a -> a) -> a -> Nat -> a;
expByNatOp :: (MonadLazy (EvalM l), VMonad l, Show (Extra l)) => BasePrims l -> Prim l
expByNatOp bp =
  tvalFun   $ \tp ->
  strictFun $ \one ->
  strictFun $ \mul ->
  strictFun $ \x   ->
  strictFun $ \e ->
  PrimExcept $
  case e of
    VBVToNat _sz w | bpIsSymbolicEvaluator bp -> lift $
      do let loop acc [] = return acc
             loop acc (b:bs)
               | Just False <- bpAsBool bp b
               = do sq <- applyAll mul [ ready acc, ready acc ]
                    loop sq bs
               | Just True <- bpAsBool bp b
               = do sq   <- applyAll mul [ ready acc, ready acc ]
                    sq_x <- applyAll mul [ ready sq, ready x ]
                    loop sq_x bs
               | otherwise
               = do sq   <- applyAll mul [ ready acc, ready acc ]
                    sq_x <- applyAll mul [ ready sq, ready x ]
                    acc' <- muxValue bp tp b sq_x sq
                    loop acc' bs

         loop one . V.toList =<< toBits (bpUnpack bp) w

    -- This can't really be implemented, we should throw an unsupported exception
    -- of some kind instead
    VIntToNat _ | bpIsSymbolicEvaluator bp -> panic "expByNat: symbolic integer"

    VNat n ->
      do let loop acc [] = return acc
             loop acc (False:bs) =
               do sq <- applyAll mul [ ready acc, ready acc ]
                  loop sq bs
             loop acc (True:bs) =
               do sq   <- applyAll mul [ ready acc, ready acc ]
                  sq_x <- applyAll mul [ ready sq, ready x ]
                  loop sq_x bs

             w = toInteger (widthNat n)

         if w > toInteger (maxBound :: Int) then
           panic "expByNatOp" ["Exponent too large", show n]
         else
           lift (loop one [ testBit n (fromInteger i) | i <- reverse [ 0 .. w-1 ]])

    v -> throwE $ "expByNatOp: Expected Nat value " <> Text.pack (show v)



------------------------------------------------------------
-- Shifts and Rotates

-- | Barrel-shifter algorithm. Takes a list of bits in big-endian order.
--   TODO use Natural instead of Integer
shifter :: Monad m => (b -> a -> a -> m a) -> (a -> Integer -> m a) -> a -> [b] -> m a
shifter mux op = go
  where
    go x [] = return x
    go x (b : bs) = do
      x' <- op x (2 ^ length bs)
      y <- mux b x' x
      go y bs

-- shift{L,R} :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> Vec n a;
shiftOp :: forall l.
  (HasCallStack, VMonadLazy l, Show (Extra l)) =>
  BasePrims l ->
  -- TODO use Natural instead of Integer
  (Thunk l -> Vector (Thunk l) -> Integer -> Vector (Thunk l)) ->
  (VBool l -> VWord l -> Integer -> MWord l) ->
  (VBool l -> VWord l -> VWord l -> MWord l) ->
  Prim l
shiftOp bp vecOp wordIntOp wordOp =
  natFun $ \n ->
  tvalFun $ \tp ->
  primFun $ \z ->
  strictFun $ \xs ->
  strictFun $ \y ->
  PrimExcept $
    case y of
      VNat i ->
        case xs of
          VVector xv -> return $ VVector (vecOp z xv (toInteger i))
          VWord xw -> lift $ do
            zb <- toBool <$> force z
            VWord <$> wordIntOp zb xw (toInteger (min i n))
          _ -> throwE $ "shiftOp: " <> Text.pack (show xs)
      VBVToNat _sz (VVector iv) | bpIsSymbolicEvaluator bp -> do
        bs <- lift (V.toList <$> traverse (fmap toBool . force) iv)
        case xs of
          VVector xv -> VVector <$> shifter (muxVector n tp) (\v i -> return (vecOp z v i)) xv bs
          VWord xw -> lift $ do
            zb <- toBool <$> force z
            VWord <$> shifter (bpMuxWord bp) (wordIntOp zb) xw bs
          _ -> throwE $ "shiftOp: " <> Text.pack (show xs)
      VBVToNat _sz (VWord iw) | bpIsSymbolicEvaluator bp ->
        case xs of
          VVector xv -> do
            bs <- lift (V.toList <$> bpUnpack bp iw)
            VVector <$> shifter (muxVector n tp) (\v i -> return (vecOp z v i)) xv bs
          VWord xw -> lift $ do
            zb <- toBool <$> force z
            VWord <$> wordOp zb xw iw
          _ -> throwE $ "shiftOp: " <> Text.pack (show xs)

      VIntToNat _i | bpIsSymbolicEvaluator bp -> panic "shiftOp: symbolic integer TODO"

      _ -> throwE $ "shiftOp: " <> Text.pack (show y)
  where
    muxVector :: Natural -> TValue l -> VBool l ->
      Vector (Thunk l) -> Vector (Thunk l) -> ExceptT Text (EvalM l) (Vector (Thunk l))
    muxVector n tp b v1 v2 = toVector (bpUnpack bp) =<< muxVal (VVecType n tp) b (VVector v1) (VVector v2)

    muxVal :: TValue l -> VBool l -> Value l -> Value l -> ExceptT Text (EvalM l) (Value l)
    muxVal tv p x y = lift (muxValue bp tv p x y)

-- rotate{L,R} :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
rotateOp :: forall l.
  (HasCallStack, VMonadLazy l, Show (Extra l)) =>
  BasePrims l ->
  --   TODO use Natural instead of Integer?
  (Vector (Thunk l) -> Integer -> Vector (Thunk l)) ->
  (VWord l -> Integer -> MWord l) ->
  (VWord l -> VWord l -> MWord l) ->
  Prim l
rotateOp bp vecOp wordIntOp wordOp =
  natFun $ \n ->
  tvalFun $ \tp ->
  strictFun $ \xs ->
  strictFun $ \y ->
  PrimExcept $
    case y of
      VNat i ->
        case xs of
          VVector xv -> return $ VVector (vecOp xv (toInteger i))
          VWord xw -> lift (VWord <$> wordIntOp xw (toInteger i))
          _ -> throwE $ "rotateOp: " <> Text.pack (show xs)
      VBVToNat _sz (VVector iv) | bpIsSymbolicEvaluator bp -> do
        bs <- lift (V.toList <$> traverse (fmap toBool . force) iv)
        case xs of
          VVector xv -> VVector <$> shifter (muxVector n tp) (\v i -> return (vecOp v i)) xv bs
          VWord xw -> lift (VWord <$> shifter (bpMuxWord bp) wordIntOp xw bs)
          _ -> throwE $ "rotateOp: " <> Text.pack (show xs)
      VBVToNat _sz (VWord iw) | bpIsSymbolicEvaluator bp ->
        case xs of
          VVector xv -> do
            bs <- lift (V.toList <$> bpUnpack bp iw)
            VVector <$> shifter (muxVector n tp) (\v i -> return (vecOp v i)) xv bs
          VWord xw -> lift (VWord <$> wordOp xw iw)
          _ -> throwE $ "rotateOp: " <> Text.pack (show xs)

      VIntToNat _i | bpIsSymbolicEvaluator bp -> panic "rotateOp: symbolic integer TODO"

      _ -> throwE $ "rotateOp: " <> Text.pack (show y)
  where
    muxVector :: HasCallStack => Natural -> TValue l -> VBool l ->
      Vector (Thunk l) -> Vector (Thunk l) -> ExceptT Text (EvalM l) (Vector (Thunk l))
    muxVector n tp b v1 v2 = toVector (bpUnpack bp) =<< lift (muxValue bp (VVecType n tp) b (VVector v1) (VVector v2))

vRotateL :: Vector a -> Integer -> Vector a
vRotateL xs i
  | V.null xs = xs
  | otherwise = (V.++) (V.drop j xs) (V.take j xs)
  where j = fromInteger (i `mod` toInteger (V.length xs))

vRotateR :: Vector a -> Integer -> Vector a
vRotateR xs i = vRotateL xs (- i)

vShiftL :: a -> Vector a -> Integer -> Vector a
vShiftL x xs i = (V.++) (V.drop j xs) (V.replicate j x)
  where j = fromInteger (i `min` toInteger (V.length xs))

vShiftR :: a -> Vector a -> Integer -> Vector a
vShiftR x xs i = (V.++) (V.replicate j x) (V.take (V.length xs - j) xs)
  where j = fromInteger (i `min` toInteger (V.length xs))

rotateLOp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Prim l
rotateLOp bp = rotateOp bp vRotateL (bpBvRolInt bp) (bpBvRol bp)

rotateROp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Prim l
rotateROp bp = rotateOp bp vRotateR (bpBvRorInt bp) (bpBvRor bp)

shiftLOp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Prim l
shiftLOp bp = shiftOp bp vShiftL (bpBvShlInt bp) (bpBvShl bp)

shiftROp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Prim l
shiftROp bp = shiftOp bp vShiftR (bpBvShrInt bp) (bpBvShr bp)


-- foldr :: (a b :: sort 0) -> (n :: Nat) -> (a -> b -> b) -> b -> Vec n a -> b;
foldrOp :: (VMonadLazy l, Show (Extra l)) => Unpack l -> Prim l
foldrOp unpack =
  constFun $
  constFun $
  constFun $
  strictFun $ \f ->
  primFun $ \z ->
  strictFun $ \xs ->
  PrimExcept $ do
    let g x m = do fx <- apply f x
                   y <- delay m
                   apply fx y
    xv <- toVector unpack xs
    lift (V.foldr g (force z) xv)

-- foldl : (a b : sort 0) -> (n : Nat) -> (b -> a -> b) -> b -> Vec n a -> b;
foldlOp :: (VMonadLazy l, Show (Extra l)) => Unpack l -> Prim l
foldlOp unpack =
  constFun $
  constFun $
  constFun $
  strictFun $ \f ->
  primFun $ \z ->
  strictFun $ \xs ->
  PrimExcept $ do
    let g m x = do f1 <- apply f =<< delay m
                   apply f1 x
    xv <- toVector unpack xs
    lift (V.foldl g (force z) xv)

-- scanl : (a b : sort 0) -> (n : Nat) -> (b -> a -> b) -> b -> Vec n a -> Vec (addNat n 1) b;
scanlOp :: forall l. (VMonadLazy l, Show (Extra l)) => Unpack l -> Prim l
scanlOp unpack =
  constFun $ -- a
  constFun $ -- b
  constFun $ -- n
  strictFun $ \f ->
  primFun $ \z ->
  strictFun $ \xs ->
  PrimExcept $ do
    let g :: Vector (Thunk l) ->
             Thunk l ->
             EvalM l (Vector (Thunk l))
        g bs v = do b <- delay (applyAll f [V.last bs, v])
                    return (V.snoc bs b)
    xv <- toVector unpack xs
    lift (VVector <$> V.foldM g (V.singleton z) xv)

-- op :: Integer -> Integer;
intUnOp :: VMonad l => (VInt l -> MInt l) -> Prim l
intUnOp f =
  intFun $ \x ->
    Prim (VInt <$> f x)

-- op :: Integer -> Integer -> Integer;
intBinOp :: VMonad l => (VInt l -> VInt l -> MInt l) -> Prim l
intBinOp f =
  intFun $ \x ->
  intFun $ \y ->
    Prim (VInt <$> f x y)

-- op :: Integer -> Integer -> Bool;
intBinCmp :: VMonad l => (VInt l -> VInt l -> MBool l) -> Prim l
intBinCmp f =
  intFun $ \x ->
  intFun $ \y ->
    Prim (VBool <$> f x y)

-- primitive intToNat :: Integer -> Nat;
intToNatOp :: (VMonad l, VInt l ~ Integer) => Prim l
intToNatOp =
  intFun $ \x -> PrimValue $!
    if x >= 0 then VNat (fromInteger x) else VNat 0

-- primitive natToInt :: Nat -> Integer;
natToIntOp :: (VMonad l, VInt l ~ Integer) => Prim l
natToIntOp = natFun $ \x -> PrimValue $ VInt (toInteger x)

-- primitive error :: (a :: sort 0) -> String -> a;
errorOp :: VMonad l => Prim l
errorOp =
  constFun $
  stringFun $ \msg ->
  Prim $ Prim.userError (Text.unpack msg)

------------------------------------------------------------
-- Conditionals

iteDepOp :: (HasCallStack, VMonadLazy l, Show (Extra l)) => BasePrims l -> Prim l
iteDepOp bp =
  primFun $ \_p ->
  boolFun $ \b ->
  primFun $ \x ->
  primFun $ \y ->
  PrimExcept $
    case bpAsBool bp b of
      Just True  -> lift (force x)
      Just False -> lift (force y)
      Nothing    -> throwE "unsupported symbolic operation: iteDep"

iteOp :: (HasCallStack, VMonadLazy l, Show (Extra l)) => BasePrims l -> Prim l
iteOp bp =
  tvalFun $ \tp ->
  boolFun $ \b ->
  primFun $ \x ->
  primFun $ \y ->
  PrimExcept $
    case bpAsBool bp b of
      Just True  -> lift (force x)
      Just False -> lift (force y)
      Nothing
        | bpIsSymbolicEvaluator bp -> lift (lazyMuxValue bp tp b (force x) (force y))
        | otherwise -> throwE "iteOp"

lazyMuxValue ::
  (HasCallStack, VMonadLazy l, Show (Extra l)) =>
  BasePrims l ->
  TValue l ->
  VBool l ->
  EvalM l (Value l) ->
  EvalM l (Value l) ->
  EvalM l (Value l)
lazyMuxValue bp tp b x y =
  case bpAsBool bp b of
    Just True  -> x
    Just False -> y
    Nothing ->
      do x' <- x
         y' <- y
         muxValue bp tp b x' y'

muxValue :: forall l.
  (HasCallStack, VMonadLazy l, Show (Extra l)) =>
  BasePrims l ->
  TValue l ->
  VBool l -> Value l -> Value l -> EvalM l (Value l)
muxValue bp tp0 b = value tp0
  where
    value :: TValue l -> Value l -> Value l -> EvalM l (Value l)
    value _ (VNat m)  (VNat n)      | m == n = return $ VNat m
    value _ (VString x) (VString y) | x == y = return $ VString x

    value (VPiType _ _tp body) (VFun nm f) (VFun _ g) =
        return $ VFun nm $ \a ->
           do tp' <- applyPiBody body a
              x <- f a
              y <- g a
              value tp' x y

    value VUnitType VUnit VUnit = return VUnit
    value (VPairType t1 t2) (VPair x1 x2) (VPair y1 y2) =
      VPair <$> thunk t1 x1 y1 <*> thunk t2 x2 y2

    value (VRecordType fs) (VRecordValue elems1) (VRecordValue elems2) =
      do let em1 = Map.fromList elems1
         let em2 = Map.fromList elems2
         let build (f,tp) = case (Map.lookup f em1, Map.lookup f em2) of
                              (Just v1, Just v2) ->
                                 do v <- thunk tp v1 v2
                                    pure (f,v)
                              _ -> panic "muxValue" ["Record field missing!", show f]
         VRecordValue <$> traverse build fs

    value (VDataType _nm _ps _ixs) (VCtorApp i ps xv) (VCtorApp j _ yv)
      | i == j = VCtorApp i ps <$> ctorArgs (primType i) ps xv yv
      | otherwise = unsupportedPrimitive "muxValue"
          ("cannot mux different data constructors " <> show i <> " " <> show j)

    value (VVecType _ tp) (VVector xv) (VVector yv) =
      VVector <$> thunks tp xv yv

    value tp (VExtra x) (VExtra y) =
      VExtra <$> bpMuxExtra bp tp b x y

    value _ (VBool x)         (VBool y)         = VBool <$> bpMuxBool bp b x y
    value _ (VWord x)         (VWord y)         = VWord <$> bpMuxWord bp b x y
    value _ (VInt x)          (VInt y)          = VInt <$> bpMuxInt bp b x y
    value _ (VArray x)        (VArray y)        = VArray <$> bpMuxArray bp b x y
    value _ (VIntMod n x)     (VIntMod _ y)     = VIntMod n <$> bpMuxInt bp b x y

    value tp x@(VWord _)       y                = do xv <- toVector' x
                                                     value tp (VVector xv) y
    value tp x                 y@(VWord _)      = do yv <- toVector' y
                                                     value tp x (VVector yv)

    value _ x@(VNat _)        y                 = nat x y
    value _ x@(VBVToNat _ _)  y                 = nat x y
    value _ x@(VIntToNat _)   y                 = nat x y

    value _ (TValue x)        (TValue y)        = TValue <$> tvalue x y

    value tp x                y                 =
      panic $ "Verifier.SAW.Simulator.Prims.iteOp: malformed arguments: " <>
         show x <> " " <> show y <> " " <> show tp

    ctorArgs :: TValue l -> [Thunk l] -> [Thunk l] -> [Thunk l] -> EvalM l [Thunk l]

    -- consume the data type parameters and compute the type of the constructor
    ctorArgs (VPiType _nm _t1 body) (p:ps) xs ys =
      do t' <- applyPiBody body p
         ctorArgs t' ps xs ys

    -- mux the arguments one at a time, as long as the constructor type is not
    -- a dependent function
    ctorArgs (VPiType _nm t1 (VNondependentPi t2)) [] (x:xs) (y:ys)=
      do z  <- thunk t1 x y
         zs <- ctorArgs t2 [] xs ys
         pure (z:zs)
    ctorArgs _ [] [] [] = pure []

    ctorArgs (VPiType _nm _t1 (VDependentPi _)) [] _ _ =
      unsupportedPrimitive "muxValue" "cannot mux constructors with dependent types"

    ctorArgs _ _ _ _ =
      panic $ "Verifier.SAW.Simulator.Prims.iteOp: constructor arguments mismtch"

    tvalue :: TValue l -> TValue l -> EvalM l (TValue l)
    tvalue (VSort x)         (VSort y)         | x == y = return $ VSort y
    tvalue x                 y                 =
      panic $ "Verifier.SAW.Simulator.Prims.iteOp: malformed arguments: "
      ++ show x ++ " " ++ show y

    toVector' :: Value l -> EvalM l (Vector (Thunk l))
    toVector' v =
      let err msg = unsupportedPrimitive "muxValue: expected vector" (Text.unpack msg)
       in runExceptT (toVector (bpUnpack bp) v) >>= either err pure

    thunks :: TValue l -> Vector (Thunk l) -> Vector (Thunk l) -> EvalM l (Vector (Thunk l))
    thunks tp xv yv
      | V.length xv == V.length yv = V.zipWithM (thunk tp) xv yv
      | otherwise                  = panic "Verifier.SAW.Simulator.Prims.iteOp: malformed arguments"

    thunk :: TValue l -> Thunk l -> Thunk l -> EvalM l (Thunk l)
    thunk tp x y = delay $
      do x' <- force x
         y' <- force y
         value tp x' y'

    nat :: Value l -> Value l -> MValue l
    nat v1 v2 =
      do let w = max (natSize v1) (natSize v2)
         x1 <- natToWord bp w v1
         x2 <- natToWord bp w v2
         VBVToNat (fromIntegral w) . VWord <$> bpMuxWord bp b x1 x2

-- fix :: (a :: sort 0) -> (a -> a) -> a;
fixOp :: (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) => Prim l
fixOp =
  constFun $
  strictFun $ \f -> Prim
    (force =<< mfix (\x -> delay (apply f x)))

------------------------------------------------------------
-- SMT Array

-- Array :: sort 0 -> sort 0 -> sort 0
arrayTypeOp :: VMonad l => Prim l
arrayTypeOp =
  tvalFun $ \a ->
  tvalFun $ \b ->
    PrimValue (TValue (VArrayType a b))

-- arrayConstant :: (a b :: sort 0) -> b -> (Array a b);
arrayConstantOp :: VMonad l => BasePrims l -> Prim l
arrayConstantOp bp =
  tvalFun $ \a ->
  tvalFun $ \b ->
  strictFun $ \e ->
    Prim (VArray <$> bpArrayConstant bp a b e)

-- arrayLookup :: (a b :: sort 0) -> (Array a b) -> a -> b;
arrayLookupOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
arrayLookupOp bp =
  constFun $
  constFun $
  strictFun $ \f ->
  strictFun $ \i -> Prim $
    do f' <- toArray f
       bpArrayLookup bp f' i

-- arrayUpdate :: (a b :: sort 0) -> (Array a b) -> a -> b -> (Array a b);
arrayUpdateOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
arrayUpdateOp bp =
  constFun $
  constFun $
  strictFun $ \f ->
  strictFun $ \i ->
  strictFun $ \e -> Prim $
    do f' <- toArray f
       VArray <$> bpArrayUpdate bp f' i e

-- arrayEq : (a b : sort 0) -> (Array a b) -> (Array a b) -> Bool;
arrayEqOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
arrayEqOp bp =
  constFun $
  constFun $
  strictFun $ \x ->
  strictFun $ \y -> Prim $
    do x' <- toArray x
       y' <- toArray y
       VBool <$> bpArrayEq bp x' y'

-- arrayCopy : (n : Nat) -> (a : sort 0) -> Array (Vec n Bool) a -> Vec n Bool -> Array (Vec n Bool) a -> Vec n Bool -> Vec n Bool -> Array (Vec n Bool) a;
arrayCopyOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
arrayCopyOp bp =
  constFun $
  constFun $
  strictFun $ \f ->
  strictFun $ \i ->
  strictFun $ \g ->
  strictFun $ \j ->
  strictFun $ \l -> Prim $
    do f' <- toArray f
       i' <- toWord (bpPack bp) i
       g' <- toArray g
       j' <- toWord (bpPack bp) j
       l' <- toWord (bpPack bp) l
       VArray <$> (bpArrayCopy bp) f' i' g' j' l'

-- arraySet : (n : Nat) -> (a : sort 0) -> Array (Vec n Bool) a -> Vec n Bool -> a -> Vec n Bool -> Array (Vec n Bool) a;
arraySetOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
arraySetOp bp =
  constFun $
  constFun $
  strictFun $ \f ->
  strictFun $ \i ->
  strictFun $ \e ->
  strictFun $ \l -> Prim $
    do f' <- toArray f
       i' <- toWord (bpPack bp) i
       l' <- toWord (bpPack bp) l
       VArray <$> (bpArraySet bp) f' i' e l'

-- arrayRangeEq : (n : Nat) -> (a : sort 0) -> Array (Vec n Bool) a -> Vec n Bool -> Array (Vec n Bool) a -> Vec n Bool -> Vec n Bool -> Bool;
arrayRangeEqOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Prim l
arrayRangeEqOp bp =
  constFun $
  constFun $
  strictFun $ \f ->
  strictFun $ \i ->
  strictFun $ \g ->
  strictFun $ \j ->
  strictFun $ \l -> Prim $
    do f' <- toArray f
       i' <- toWord (bpPack bp) i
       g' <- toArray g
       j' <- toWord (bpPack bp) j
       l' <- toWord (bpPack bp) l
       VBool <$> (bpArrayRangeEq bp) f' i' g' j' l'
