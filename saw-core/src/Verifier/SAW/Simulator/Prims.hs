{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

{- |
Module      : Verifier.SAW.Simulator.Prims
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.Prims where

import Prelude hiding (sequence, mapM)

import GHC.Stack( HasCallStack )

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Monad (foldM, liftM, zipWithM, unless)
import Control.Monad.Fix (MonadFix(mfix))
import Data.Bits
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Traversable
import Data.Vector (Vector)
import qualified Data.Vector as V
import Numeric.Natural (Natural)

import Verifier.SAW.Term.Functor (Ident, alistAllFields)
import Verifier.SAW.Simulator.Value
import Verifier.SAW.Prim
import qualified Verifier.SAW.Prim as Prim

import qualified Verifier.SAW.Utils as Panic (panic)

------------------------------------------------------------
--

-- | A collection of implementations of primitives on base types.
-- These can be used to derive other primitives on higher types.
data BasePrims l =
  BasePrims
  { bpAsBool :: VBool l -> Maybe Bool
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
  , bpMuxExtra :: VBool l -> Extra l -> Extra l -> EvalM l (Extra l)
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
  , bpArrayConstant :: TValue l -> Value l -> MArray l
  , bpArrayLookup :: VArray l -> Value l -> MValue l
  , bpArrayUpdate :: VArray l -> Value l -> Value l -> MArray l
  , bpArrayEq :: VArray l -> VArray l -> MBool l
  }

bpBool :: VMonad l => BasePrims l -> Bool -> MBool l
bpBool bp True = return (bpTrue bp)
bpBool bp False = return (bpFalse bp)

-- | Given implementations of the base primitives, construct a table
-- containing implementations of all primitives.
constMap ::
  forall l.
  (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) =>
  BasePrims l -> Map Ident (Value l)
constMap bp = Map.fromList
  -- Boolean
  [ ("Prelude.Bool"  , TValue VBoolType)
  , ("Prelude.True"  , VBool (bpTrue bp))
  , ("Prelude.False" , VBool (bpFalse bp))
  , ("Prelude.not"   , strictFun (liftM VBool . bpNot bp . toBool))
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
  , ("Prelude.bvForall", natFun $ \n ->
        pure . strictFun $ fmap VBool . bpBvForall bp n . toWordPred
    )

{-
  -- Shifts
  , ("Prelude.bvShl" , bvShLOp)
  , ("Prelude.bvShr" , bvShROp)
  , ("Prelude.bvSShr", bvSShROp)
-}
  -- Nat
  , ("Prelude.Succ", succOp)
  , ("Prelude.addNat", addNatOp)
  , ("Prelude.subNat", subNatOp bp)
  , ("Prelude.mulNat", mulNatOp)
  , ("Prelude.minNat", minNatOp)
  , ("Prelude.maxNat", maxNatOp)
  , ("Prelude.divModNat", divModNatOp)
  , ("Prelude.expNat", expNatOp)
  , ("Prelude.widthNat", widthNatOp)
  , ("Prelude.natCase", natCaseOp)
  , ("Prelude.equalNat", equalNatOp bp)
  , ("Prelude.ltNat", ltNatOp bp)
  -- Integers
  , ("Prelude.Integer", TValue VIntType)
  , ("Prelude.intAdd", intBinOp "intAdd" (bpIntAdd bp))
  , ("Prelude.intSub", intBinOp "intSub" (bpIntSub bp))
  , ("Prelude.intMul", intBinOp "intMul" (bpIntMul bp))
  , ("Prelude.intDiv", intBinOp "intDiv" (bpIntDiv bp))
  , ("Prelude.intMod", intBinOp "intMod" (bpIntMod bp))
  , ("Prelude.intNeg", intUnOp  "intNeg" (bpIntNeg bp))
  , ("Prelude.intAbs", intUnOp  "intAbs" (bpIntAbs bp))
  , ("Prelude.intEq" , intBinCmp "intEq" (bpIntEq bp))
  , ("Prelude.intLe" , intBinCmp "intLe" (bpIntLe bp))
  , ("Prelude.intLt" , intBinCmp "intLt" (bpIntLt bp))
{-
  --XXX , ("Prelude.intToNat", Prims.intToNatOp)
  , ("Prelude.natToInt", natToIntOp)
  , ("Prelude.intToBv" , intToBvOp)
  , ("Prelude.bvToInt" , bvToIntOp)
  , ("Prelude.sbvToInt", sbvToIntOp)
  --XXX , ("Prelude.intMin"  , Prims.intMinOp)
  --XXX , ("Prelude.intMax"  , Prims.intMaxOp)
-}
  , ("Prelude.intMin", intBinOp "intMin" (bpIntMin bp))
  , ("Prelude.intMax", intBinOp "intMax" (bpIntMax bp))
  -- Modular Integers
  , ("Prelude.IntMod", natFun $ \n -> pure $ TValue (VIntModType n))
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
  , ("Prelude.rotateL", rotateLOp bp)
  , ("Prelude.rotateR", rotateROp bp)
  , ("Prelude.shiftL", shiftLOp bp)
  , ("Prelude.shiftR", shiftROp bp)
  , ("Prelude.EmptyVec", emptyVec)
  -- Miscellaneous
  , ("Prelude.coerce", coerceOp)
  , ("Prelude.bvNat", bvNatOp bp)
  , ("Prelude.bvToNat", bvToNatOp)
  , ("Prelude.error", errorOp)
  , ("Prelude.fix", fixOp)
  -- Overloaded
  , ("Prelude.ite", iteOp bp)
  , ("Prelude.iteDep", iteOp bp)
  -- SMT Arrays
  , ("Prelude.Array", arrayTypeOp)
  , ("Prelude.arrayConstant", arrayConstantOp bp)
  , ("Prelude.arrayLookup", arrayLookupOp bp)
  , ("Prelude.arrayUpdate", arrayUpdateOp bp)
  , ("Prelude.arrayEq", arrayEqOp bp)
  ]

-- | Call this function to indicate that a programming error has
-- occurred, e.g. a datatype invariant has been violated.
panic :: HasCallStack => String -> a
panic msg = Panic.panic "Verifier.SAW.Simulator.Prims" [msg]

------------------------------------------------------------
-- Value accessors and constructors

vNat :: Natural -> Value l
vNat n = VNat n

natFromValue :: Value l -> Natural
natFromValue (VNat n) = n
natFromValue _ = panic "natFromValue"

natFun'' :: (HasCallStack, VMonad l, Show (Extra l)) => String -> (Natural -> MValue l) -> Value l
natFun'' s f = strictFun g
  where g (VNat n) = f n
        g v = panic $ "expected Nat (" ++ s ++ "): " ++ show v

natFun' :: (HasCallStack, VMonad l) => String -> (Natural -> MValue l) -> Value l
natFun' s f = strictFun g
  where g (VNat n) = f n
        g _ = panic $ "expected Nat: " ++ s

natFun :: (HasCallStack, VMonad l) => (Natural -> MValue l) -> Value l
natFun f = strictFun g
  where g (VNat n) = f n
        g _ = panic "expected Nat"

intFun :: VMonad l => String -> (VInt l -> MValue l) -> Value l
intFun msg f = strictFun g
  where g (VInt i) = f i
        g _ = panic $ "expected Integer "++ msg

intModFun :: VMonad l => String -> (VInt l -> MValue l) -> Value l
intModFun msg f = strictFun g
  where g (VIntMod _ i) = f i
        g _ = panic $ "expected IntMod "++ msg

toBool :: Show (Extra l) => Value l -> VBool l
toBool (VBool b) = b
toBool x = panic $ unwords ["Verifier.SAW.Simulator.toBool", show x]

type Pack l   = Vector (VBool l) -> MWord l
type Unpack l = VWord l -> EvalM l (Vector (VBool l))

toWord :: (VMonad l, Show (Extra l)) => Pack l -> Value l -> MWord l
toWord _ (VWord w) = return w
toWord pack (VVector vv) = pack =<< V.mapM (liftM toBool . force) vv
toWord _ x = panic $ unwords ["Verifier.SAW.Simulator.toWord", show x]

toWordPred :: (VMonad l, Show (Extra l)) => Value l -> VWord l -> MBool l
toWordPred (VFun f) = fmap toBool . f . ready . VWord
toWordPred x = panic $ unwords ["Verifier.SAW.Simulator.toWordPred", show x]

toBits :: (VMonad l, Show (Extra l)) => Unpack l -> Value l ->
                                                  EvalM l (Vector (VBool l))
toBits unpack (VWord w) = unpack w
toBits _ (VVector v) = V.mapM (liftM toBool . force) v
toBits _ x = panic $ unwords ["Verifier.SAW.Simulator.toBits", show x]

toVector :: (VMonad l, Show (Extra l)) => Unpack l
         -> Value l -> EvalM l (Vector (Thunk l))
toVector _ (VVector v) = return v
toVector unpack (VWord w) = liftM (fmap (ready . VBool)) (unpack w)
toVector _ x = panic $ unwords ["Verifier.SAW.Simulator.toVector", show x]

wordFun :: (VMonad l, Show (Extra l)) => Pack l -> (VWord l -> MValue l) -> Value l
wordFun pack f = strictFun (\x -> toWord pack x >>= f)

bitsFun :: (VMonad l, Show (Extra l)) =>
  Unpack l -> (Vector (VBool l) -> MValue l) -> Value l
bitsFun unpack f = strictFun (\x -> toBits unpack x >>= f)

vectorFun :: (VMonad l, Show (Extra l)) =>
  Unpack l -> (Vector (Thunk l) -> MValue l) -> Value l
vectorFun unpack f = strictFun (\x -> toVector unpack x >>= f)

vecIdx :: a -> Vector a -> Int -> a
vecIdx err v n =
  case (V.!?) v n of
    Just a -> a
    Nothing -> err

toArray :: (VMonad l, Show (Extra l)) => Value l -> MArray l
toArray (VArray f) = return f
toArray x = panic $ unwords ["Verifier.SAW.Simulator.toArray", show x]

------------------------------------------------------------
-- Standard operator types

-- op :: Bool -> Bool -> Bool;
boolBinOp ::
  (VMonad l, Show (Extra l)) =>
  (VBool l -> VBool l -> MBool l) -> Value l
boolBinOp op =
  strictFun $ \x -> return $
  strictFun $ \y -> VBool <$> op (toBool x) (toBool y)

-- op : (n : Nat) -> Vec n Bool -> Vec n Bool;
wordUnOp ::
  (VMonad l, Show (Extra l)) =>
  Pack l -> (VWord l -> MWord l) -> Value l
wordUnOp pack op =
  constFun $
  strictFun $ \x ->
  do xw <- toWord pack x
     VWord <$> op xw

-- op : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
wordBinOp ::
  (VMonad l, Show (Extra l)) =>
  Pack l -> (VWord l -> VWord l -> MWord l) -> Value l
wordBinOp pack op =
  constFun $
  strictFun $ \x -> return $
  strictFun $ \y ->
  do xw <- toWord pack x
     yw <- toWord pack y
     VWord <$> op xw yw

-- op : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool;
wordBinRel ::
  (VMonad l, Show (Extra l)) =>
  Pack l -> (VWord l -> VWord l -> MBool l) -> Value l
wordBinRel pack op =
  constFun $
  strictFun $ \x -> return $
  strictFun $ \y ->
  do xw <- toWord pack x
     yw <- toWord pack y
     VBool <$> op xw yw

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
bvNatOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
bvNatOp bp =
  natFun'' "bvNatOp1" $ \w -> return $
  natFun'' "bvNatOp2"  $ \x ->
  VWord <$> bpBvLit bp (fromIntegral w) (toInteger x) -- FIXME check for overflow on w

-- bvToNat : (n : Nat) -> Vec n Bool -> Nat;
bvToNatOp :: VMonad l => Value l
bvToNatOp =
  natFun' "bvToNat" $ \n -> return $
  pureFun (VBVToNat (fromIntegral n)) -- TODO, bad fromIntegral

-- coerce :: (a b :: sort 0) -> Eq (sort 0) a b -> a -> b;
coerceOp :: VMonad l => Value l
coerceOp =
  constFun $
  constFun $
  constFun $
  VFun force

------------------------------------------------------------
-- Nat primitives

-- | Return the number of bits necessary to represent the given value,
-- which should be a value of type Nat.
natSize :: BasePrims l -> Value l -> Natural
natSize _bp val =
  case val of
    VNat n -> widthNat n
    VBVToNat n _ -> fromIntegral n -- TODO, remove this fromIntegral 
    VIntToNat _ -> error "natSize: symbolic integer"
    _ -> panic "natSize: expected Nat"

-- | Convert the given value (which should be of type Nat) to a word
-- of the given bit-width. The bit-width must be at least as large as
-- that returned by @natSize@.
natToWord :: (VMonad l, Show (Extra l)) => BasePrims l -> Int -> Value l -> MWord l
natToWord bp w val =
  case val of
    VNat n -> bpBvLit bp w (toInteger n)
    VIntToNat _i -> error "natToWord of VIntToNat TODO!"
    VBVToNat xsize v ->
      do x <- toWord (bpPack bp) v
         case compare xsize w of
           GT -> panic "natToWord: not enough bits"
           EQ -> return x
           LT -> -- zero-extend x to width w
             do pad <- bpBvLit bp (w - xsize) 0
                bpBvJoin bp pad x
    _ -> panic "natToWord: expected Nat"

-- Succ :: Nat -> Nat;
succOp :: VMonad l => Value l
succOp =
  natFun' "Succ" $ \n -> return $
  vNat (succ n)

-- addNat :: Nat -> Nat -> Nat;
addNatOp :: VMonad l => Value l
addNatOp =
  natFun' "addNat1" $ \m -> return $
  natFun' "addNat2" $ \n -> return $
  vNat (m + n)

-- subNat :: Nat -> Nat -> Nat;
subNatOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
subNatOp bp =
  strictFun $ \x -> return $
  strictFun $ \y -> g x y
  where
    g (VNat i) (VNat j) = return $ VNat (if i < j then 0 else i - j)
    g v1 v2 =
      do let w = toInteger (max (natSize bp v1) (natSize bp v2))
         unless (w <= toInteger (maxBound :: Int))
                (panic "subNatOp" ["width too large", show w])
         x1 <- natToWord bp (fromInteger w) v1
         x2 <- natToWord bp (fromInteger w) v2
         lt <- bpBvult bp x1 x2
         z <- bpBvLit bp (fromInteger w) 0
         d <- bpBvSub bp x1 x2
         VBVToNat (fromInteger w) . VWord <$> bpMuxWord bp lt z d -- TODO, boo fromInteger

-- mulNat :: Nat -> Nat -> Nat;
mulNatOp :: VMonad l => Value l
mulNatOp =
  natFun' "mulNat1" $ \m -> return $
  natFun' "mulNat2" $ \n -> return $
  vNat (m * n)

-- minNat :: Nat -> Nat -> Nat;
minNatOp :: VMonad l => Value l
minNatOp =
  natFun' "minNat1" $ \m -> return $
  natFun' "minNat2" $ \n -> return $
  vNat (min m n)

-- maxNat :: Nat -> Nat -> Nat;
maxNatOp :: VMonad l => Value l
maxNatOp =
  natFun' "maxNat1" $ \m -> return $
  natFun' "maxNat2" $ \n -> return $
  vNat (max m n)

-- divModNat :: Nat -> Nat -> #(Nat, Nat);
divModNatOp :: VMonad l => Value l
divModNatOp =
  natFun' "divModNat1" $ \m -> return $
  natFun' "divModNat2" $ \n -> return $
    let (q,r) = divMod m n in
    vTuple [ready $ vNat q, ready $ vNat r]

-- expNat :: Nat -> Nat -> Nat;
expNatOp :: VMonad l => Value l
expNatOp =
  natFun' "expNat1" $ \m -> return $
  natFun' "expNat2" $ \n -> return $
  vNat (m ^ n)

-- widthNat :: Nat -> Nat;
widthNatOp :: VMonad l => Value l
widthNatOp =
  natFun' "widthNat1" $ \n -> return $
  vNat (widthNat n)

-- equalNat :: Nat -> Nat -> Bool;
equalNatOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
equalNatOp bp =
  strictFun $ \x -> return $
  strictFun $ \y -> g x y
  where
    g (VNat i) (VNat j) = VBool <$> bpBool bp (i == j)
    g v1 v2 =
      do let w = toInteger (max (natSize bp v1) (natSize bp v2))
         unless (w <= toInteger (maxBound :: Int))
                (panic "equalNatOp" ["width too large", show w])
         x1 <- natToWord bp (fromInteger w) v1
         x2 <- natToWord bp (fromInteger w) v2
         VBool <$> bpBvEq bp x1 x2

-- ltNat :: Nat -> Nat -> Bool;
ltNatOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
ltNatOp bp =
  strictFun $ \x -> return $
  strictFun $ \y -> g x y
  where
    g (VNat i) (VNat j) = VBool <$> bpBool bp (i < j)
    g v1 v2 =
      do let w = toInteger (max (natSize bp v1) (natSize bp v2))
         unless (w <= toInteger (maxBound :: Int))
                (panic "ltNatOp" ["width too large", show w])
         x1 <- natToWord bp (fromInteger w) v1
         x2 <- natToWord bp (fromInteger w) v2
         VBool <$> bpBvult bp x1 x2

-- natCase :: (p :: Nat -> sort 0) -> p Zero -> ((n :: Nat) -> p (Succ n)) -> (n :: Nat) -> p n;
natCaseOp :: (VMonad l, Show (Extra l)) => Value l
natCaseOp =
  constFun $
  VFun $ \z -> return $
  VFun $ \s -> return $
  natFun' "natCase" $ \n ->
    if n == 0
    then force z
    else do s' <- force s
            apply s' (ready (VNat (n - 1)))

--------------------------------------------------------------------------------

-- Vec :: (n :: Nat) -> (a :: sort 0) -> sort 0;
vecTypeOp :: VMonad l => Value l
vecTypeOp =
  natFun' "VecType" $ \n -> return $
  pureFun $ \a -> TValue (VVecType n (toTValue a))

-- gen :: (n :: Nat) -> (a :: sort 0) -> (Nat -> a) -> Vec n a;
genOp :: (VMonadLazy l, Show (Extra l)) => Value l
genOp =
  natFun' "gen1" $ \n -> return $
  constFun $
  strictFun $ \f -> do
    let g i = delay $ apply f (ready (VNat (fromIntegral i)))
    if toInteger n > toInteger (maxBound :: Int) then
      panic ("Verifier.SAW.Simulator.gen: vector size too large: " ++ show n)
      else liftM VVector $ V.generateM (fromIntegral n) g

-- eq :: (a :: sort 0) -> a -> a -> Bool
eqOp :: forall l. (VMonadLazy l, Show (Extra l)) => BasePrims l -> Value l
eqOp bp =
  constFun $ pureFun $ \v1 -> strictFun $ \v2 -> VBool <$> go v1 v2
  where
    go :: Value l -> Value l -> MBool l
    go VUnit VUnit = return (bpTrue bp)
    go (VPair x1 x2) (VPair y1 y2) =
      do b1 <- go' x1 y1
         b2 <- go' x2 y2
         bpAnd bp b1 b2
    go (VWord w1) (VWord w2) = bpBvEq bp w1 w2
    go (VVector v1) (VVector v2) =
      do bs <- sequence $ zipWith go' (V.toList v1) (V.toList v2)
         foldM (bpAnd bp) (bpTrue bp) bs
    go x1 (VVector v2) =
      do v1 <- toVector (bpUnpack bp) x1
         go (VVector v1) (VVector v2)
    go (VVector v1) x2 =
      do v2 <- toVector (bpUnpack bp) x2
         go (VVector v1) (VVector v2)
    go (VRecordValue elems1) (VRecordValue
                              (alistAllFields (map fst elems1) -> Just elems2)) =
      zipWithM go' (map snd elems1) elems2 >>= foldM (bpAnd bp) (bpTrue bp)
    go (VBool b1) (VBool b2) = bpBoolEq bp b1 b2
    go (VInt i1) (VInt i2) = bpIntEq bp i1 i2
    go (VArray f1) (VArray f2) = bpArrayEq bp f1 f2
    go x1 x2 = panic $ "eq: invalid arguments: " ++ show (x1, x2)

    go' :: Thunk l -> Thunk l -> MBool l
    go' thunk1 thunk2 =
      do v1 <- force thunk1
         v2 <- force thunk2
         go v1 v2

-- atWithDefault :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> a;
atWithDefaultOp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Value l
atWithDefaultOp bp =
  natFun $ \n -> return $
  constFun $
  VFun $ \d -> return $
  strictFun $ \x -> return $
  strictFun $ \idx ->
    case idx of
      VNat i ->
        case x of
          VVector xv -> force (vecIdx d xv (fromIntegral i)) -- FIXME dangerous fromIntegral
          VWord xw -> VBool <$> bpBvAt bp xw (fromIntegral i) -- FIXME dangerous fromIntegral
          _ -> panic "atOp: expected vector"
      VBVToNat _sz i -> do
        iv <- toBits (bpUnpack bp) i
        case x of
          VVector xv ->
            selectV (lazyMuxValue bp) (fromIntegral n - 1) (force . vecIdx d xv) iv -- FIXME dangerous fromIntegral
          VWord xw ->
            selectV (lazyMuxValue bp) (fromIntegral n - 1) (liftM VBool . bpBvAt bp xw) iv -- FIXME dangerous fromIntegral
          _ -> panic "atOp: expected vector"

      VIntToNat _i ->
        error "atWithDefault: symbolic integer TODO"

      _ -> panic $ "atOp: expected Nat, got " ++ show idx

-- upd :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a -> Vec n a;
updOp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Value l
updOp bp =
  natFun $ \n -> return $
  constFun $
  vectorFun (bpUnpack bp) $ \xv -> return $
  strictFun $ \idx -> return $
  VFun $ \y ->
    case idx of
      VNat i
        | toInteger i < toInteger (V.length xv)
           -> return (VVector (xv V.// [(fromIntegral i, y)]))
        | otherwise                   -> return (VVector xv)
      VBVToNat wsize (VWord w) ->
        do let f i = do b <- bpBvEq bp w =<< bpBvLit bp wsize (toInteger i)
                        if wsize < 64 && toInteger i >= 2 ^ wsize
                          then return (xv V.! i)
                          else delay (lazyMuxValue bp b (force y) (force (xv V.! i)))
           yv <- V.generateM (V.length xv) f
           return (VVector yv)
      VBVToNat _sz (VVector iv) ->
        do let update i = return (VVector (xv V.// [(i, y)]))
           iv' <- V.mapM (liftM toBool . force) iv
           selectV (lazyMuxValue bp) (fromIntegral n - 1) update iv' -- FIXME dangerous fromIntegral

      VIntToNat _ -> error "updOp: symbolic integer TODO"

      _ -> panic $ "updOp: expected Nat, got " ++ show idx

-- primitive EmptyVec :: (a :: sort 0) -> Vec 0 a;
emptyVec :: VMonad l => Value l
emptyVec = constFun $ VVector V.empty

-- take :: (a :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) a -> Vec m a;
takeOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
takeOp bp =
  constFun $
  natFun $ \(fromIntegral -> m) -> return $ -- FIXME dangerous fromIntegral
  constFun $
  strictFun $ \v ->
    case v of
      VVector vv -> return (VVector (V.take m vv))
      VWord vw -> VWord <$> bpBvSlice bp 0 m vw
      _ -> panic $ "takeOp: " ++ show v

-- drop :: (a :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) a -> Vec n a;
dropOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
dropOp bp =
  constFun $
  natFun $ \(fromIntegral -> m) -> return $ -- FIXME dangerous fromIntegral
  constFun $
  strictFun $ \v ->
  case v of
    VVector vv -> return (VVector (V.drop m vv))
    VWord vw -> VWord <$> bpBvSlice bp m (bpBvSize bp vw - m) vw
    _ -> panic $ "dropOp: " ++ show v

-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
appendOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
appendOp bp =
  constFun $
  constFun $
  constFun $
  strictFun $ \xs -> return $
  strictFun $ \ys ->
  appV bp xs ys

appV :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l -> Value l -> MValue l
appV bp xs ys =
  case (xs, ys) of
    (VVector xv, _) | V.null xv -> return ys
    (_, VVector yv) | V.null yv -> return xs
    (VWord xw, VWord yw) -> VWord <$> bpBvJoin bp xw yw
    (VVector xv, VVector yv) -> return $ VVector ((V.++) xv yv)
    (VVector xv, VWord yw) -> liftM (\yv -> VVector ((V.++) xv (fmap (ready . VBool) yv))) (bpUnpack bp yw)
    (VWord xw, VVector yv) -> liftM (\xv -> VVector ((V.++) (fmap (ready . VBool) xv) yv)) (bpUnpack bp xw)
    _ -> panic $ "Verifier.SAW.Simulator.Prims.appendOp: " ++ show xs ++ ", " ++ show ys

-- join  :: (m n :: Nat) -> (a :: sort 0) -> Vec m (Vec n a) -> Vec (mulNat m n) a;
joinOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
joinOp bp =
  constFun $
  constFun $
  constFun $
  strictFun $ \x ->
  case x of
    VVector xv -> do
      vv <- V.mapM force xv
      V.foldM (appV bp) (VVector V.empty) vv
    _ -> panic "Verifier.SAW.Simulator.Prims.joinOp"

-- split :: (m n :: Nat) -> (a :: sort 0) -> Vec (mulNat m n) a -> Vec m (Vec n a);
splitOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
splitOp bp =
  natFun $ \(fromIntegral -> m) -> return $ -- FIXME dangerous fromIntegral
  natFun $ \(fromIntegral -> n) -> return $ -- FIXME dangerous fromIntegral
  constFun $
  strictFun $ \x ->
  case x of
    VVector xv ->
      let f i = ready (VVector (V.slice (i*n) n xv))
      in return (VVector (V.generate m f))
    VWord xw ->
      let f i = (ready . VWord) <$> bpBvSlice bp (i*n) n xw
      in VVector <$> V.generateM m f
    _ -> panic "Verifier.SAW.Simulator.SBV.splitOp"

-- vZip :: (a b :: sort 0) -> (m n :: Nat) -> Vec m a -> Vec n b -> Vec (minNat m n) #(a, b);
vZipOp :: (VMonadLazy l, Show (Extra l)) => Unpack l -> Value l
vZipOp unpack =
  constFun $
  constFun $
  constFun $
  constFun $
  strictFun $ \x -> return $
  strictFun $ \y ->
  do xv <- toVector unpack x
     yv <- toVector unpack y
     let pair a b = ready (vTuple [a, b])
     return (VVector (V.zipWith pair xv yv))


--------------------------------------------------------------------------
-- Generic square-and-multiply

-- primitive expByNat : (a:sort 0) -> a -> (a -> a -> a) -> a -> Nat -> a;
expByNatOp :: (MonadLazy (EvalM l), VMonad l, Show (Extra l)) => BasePrims l -> Value l
expByNatOp bp =
  constFun $
  pureFun $ \one ->
  pureFun $ \mul ->
  pureFun $ \x   ->
  strictFun $ \case
    VBVToNat _sz w ->
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
                    acc' <- muxValue bp b sq_x sq
                    loop acc' bs

         loop one . V.toList =<< toBits (bpUnpack bp) w

    VIntToNat _ -> error "expByNat: symbolic integer"

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
           loop one [ testBit n (fromInteger i) | i <- reverse [ 0 .. w-1 ]]

    v -> panic "expByNatOp" [ "Expected Nat value", show v ]



------------------------------------------------------------
-- Shifts and Rotates

-- | Barrel-shifter algorithm. Takes a list of bits in big-endian order.
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
  (VMonadLazy l, Show (Extra l)) =>
  BasePrims l ->
  (Thunk l -> Vector (Thunk l) -> Integer -> Vector (Thunk l)) ->
  (VBool l -> VWord l -> Integer -> MWord l) ->
  (VBool l -> VWord l -> VWord l -> MWord l) ->
  Value l
shiftOp bp vecOp wordIntOp wordOp =
  natFun $ \n -> return $
  constFun $
  VFun $ \z -> return $
  strictFun $ \xs -> return $
  strictFun $ \y ->
    case y of
      VNat i ->
        case xs of
          VVector xv -> return $ VVector (vecOp z xv (toInteger i))
          VWord xw -> do
            zb <- toBool <$> force z
            VWord <$> wordIntOp zb xw (toInteger (min i n))
          _ -> panic $ "shiftOp: " ++ show xs
      VBVToNat _sz (VVector iv) -> do
        bs <- V.toList <$> traverse (fmap toBool . force) iv
        case xs of
          VVector xv -> VVector <$> shifter muxVector (\v i -> return (vecOp z v i)) xv bs
          VWord xw -> do
            zb <- toBool <$> force z
            VWord <$> shifter (bpMuxWord bp) (wordIntOp zb) xw bs
          _ -> panic $ "shiftOp: " ++ show xs
      VBVToNat _sz (VWord iw) ->
        case xs of
          VVector xv -> do
            bs <- V.toList <$> bpUnpack bp iw
            VVector <$> shifter muxVector (\v i -> return (vecOp z v i)) xv bs
          VWord xw -> do
            zb <- toBool <$> force z
            VWord <$> wordOp zb xw iw
          _ -> panic $ "shiftOp: " ++ show xs

      VIntToNat _i -> error "shiftOp: symbolic integer TODO"

      _ -> panic $ "shiftOp: " ++ show y
  where
    muxVector :: VBool l -> Vector (Thunk l) -> Vector (Thunk l) -> EvalM l (Vector (Thunk l))
    muxVector b v1 v2 = toVector (bpUnpack bp) =<< muxVal b (VVector v1) (VVector v2)

    muxVal :: VBool l -> Value l -> Value l -> MValue l
    muxVal = muxValue bp

-- rotate{L,R} :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
rotateOp :: forall l.
  (VMonadLazy l, Show (Extra l)) =>
  BasePrims l ->
  (Vector (Thunk l) -> Integer -> Vector (Thunk l)) ->
  (VWord l -> Integer -> MWord l) ->
  (VWord l -> VWord l -> MWord l) ->
  Value l
rotateOp bp vecOp wordIntOp wordOp =
  constFun $
  constFun $
  strictFun $ \xs -> return $
  strictFun $ \y ->
    case y of
      VNat i ->
        case xs of
          VVector xv -> return $ VVector (vecOp xv (toInteger i))
          VWord xw -> VWord <$> wordIntOp xw (toInteger i)
          _ -> panic $ "rotateOp: " ++ show xs
      VBVToNat _sz (VVector iv) -> do
        bs <- V.toList <$> traverse (fmap toBool . force) iv
        case xs of
          VVector xv -> VVector <$> shifter muxVector (\v i -> return (vecOp v i)) xv bs
          VWord xw -> VWord <$> shifter (bpMuxWord bp) wordIntOp xw bs
          _ -> panic $ "rotateOp: " ++ show xs
      VBVToNat _sz (VWord iw) ->
        case xs of
          VVector xv -> do
            bs <- V.toList <$> bpUnpack bp iw
            VVector <$> shifter muxVector (\v i -> return (vecOp v i)) xv bs
          VWord xw -> do
            VWord <$> wordOp xw iw
          _ -> panic $ "rotateOp: " ++ show xs

      VIntToNat _i -> error "rotateOp: symbolic integer TODO"

      _ -> panic $ "rotateOp: " ++ show y
  where
    muxVector :: VBool l -> Vector (Thunk l) -> Vector (Thunk l) -> EvalM l (Vector (Thunk l))
    muxVector b v1 v2 = toVector (bpUnpack bp) =<< muxVal b (VVector v1) (VVector v2)

    muxVal :: VBool l -> Value l -> Value l -> MValue l
    muxVal = muxValue bp

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

rotateLOp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Value l
rotateLOp bp = rotateOp bp vRotateL (bpBvRolInt bp) (bpBvRol bp)

rotateROp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Value l
rotateROp bp = rotateOp bp vRotateR (bpBvRorInt bp) (bpBvRor bp)

shiftLOp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Value l
shiftLOp bp = shiftOp bp vShiftL (bpBvShlInt bp) (bpBvShl bp)

shiftROp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Value l
shiftROp bp = shiftOp bp vShiftR (bpBvShrInt bp) (bpBvShr bp)

{-
-- rotate{L,R} :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
shiftValue :: forall l.
  (VMonadLazy l, Show (Extra l)) =>
  BasePrims l ->
  (Vector (Thunk l) -> Integer -> Vector (Thunk l)) ->
  (VWord l -> Integer -> MWord l) ->
  (VWord l -> VWord l -> MWord l) ->
  Value l -> Value l -> MValue l
shiftValue bp vecOp wordIntOp wordOp xs y =
  case y of
    VNat i ->
      case xs of
        VVector xv -> return $ VVector (vecOp xv i)
        VWord xw -> VWord <$> wordIntOp xw i
        _ -> panic $ "shift/rotate: " ++ show xs
    VToNat (VVector iv) ->
      do bs <- V.toList <$> traverse (fmap toBool . force) iv
         case xs of
           VVector xv -> VVector <$> shifter muxVector (\v i -> return (vecOp v i)) xv bs
           VWord xw -> VWord <$> shifter (bpMuxWord bp) wordIntOp xw bs
           _ -> panic $ "shift/rotate: " ++ show xs
    VToNat (VWord iw) ->
      case xs of
        VVector xv ->
          do bs <- V.toList <$> bpUnpack bp iw
             VVector <$> shifter muxVector (\v i -> return (vecOp v i)) xv bs
        VWord xw ->
          do VWord <$> wordOp xw iw
        _ -> panic $ "shift/rotate: " ++ show xs
    _ -> panic $ "shift/rotate: " ++ show y
  where
    muxVector :: VBool l -> Vector (Thunk l) -> Vector (Thunk l) -> EvalM l (Vector (Thunk l))
    muxVector b v1 v2 = toVector (bpUnpack bp) =<< muxVal b (VVector v1) (VVector v2)

    muxVal :: VBool l -> Value l -> Value l -> MValue l
    muxVal = muxValue bp
-}

{-------------

-- Concrete --

-- shiftR :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> Vec n a;
shiftROp :: CValue
shiftROp =
  constFun $
  constFun $
  VFun $ \x -> return $
  pureFun $ \xs ->
  Prims.natFun $ \i -> return $
    case xs of
      VVector xv -> VVector (vShiftR x xv (fromIntegral i))
      VWord w -> vWord (bvShiftR c w (fromIntegral i))
        where c = toBool (runIdentity (force x))
      _ -> panic $ "Verifier.SAW.Simulator.Concrete.shiftROp: " ++ show xs


-- SBV --

-- shiftR :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> Vec n a;
shiftROp :: SValue
shiftROp = shiftOp vShiftR undefined shr
  where shr b x i = svIte b (svNot (svShiftRight (svNot x) i)) (svShiftRight x i)

-- shift{L,R} :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> Vec n a;
shiftOp :: (SThunk -> Vector SThunk -> Integer -> Vector SThunk)
        -> (SBool -> SWord -> Integer -> SWord)
        -> (SBool -> SWord -> SWord -> SWord)
        -> SValue
shiftOp vecOp wordOp svOp =
  constFun $
  constFun $
  VFun $ \z -> return $
  strictFun $ \xs -> return $
  strictFun $ \y ->
    case y of
      VNat i ->
        case xs of
          VVector xv -> return $ VVector (vecOp z xv i)
          VWord xw -> do
            zv <- toBool <$> force z
            let i' = fromInteger (i `min` toInteger (intSizeOf xw))
            return $ vWord (wordOp zv xw i')
          _ -> panic $ "shiftOp: " ++ show xs
      VToNat (VVector iv) -> do
        bs <- V.toList <$> traverse (fmap toBool . force) iv
        case xs of
          VVector xv -> VVector <$> shifter muxVector (vecOp z) xv bs
          VWord xw -> do
            zv <- toBool <$> force z
            vWord <$> shifter muxWord (wordOp zv) xw bs
          _ -> panic $ "shiftOp: " ++ show xs
      VToNat (VWord iw) ->
        case xs of
          VVector xv -> do
            bs <- V.toList <$> svUnpack iw
            VVector <$> shifter muxVector (vecOp z) xv bs
          VWord xw -> do
            zv <- toBool <$> force z
            return $ vWord (svOp zv xw iw)
          _ -> panic $ "shiftOp: " ++ show xs
      _ -> panic $ "shiftOp: " ++ show y


-- RME --

-- | op :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> Vec n a;
shiftOp :: (RValue -> Vector RValue -> Integer -> Vector RValue) -> RValue
shiftOp op =
  constFun $
  constFun $
  pureFun $ \z ->
  pureFun $ \(toVector -> x) ->
  pureFun $ \y ->
  case y of
    VNat n   -> vVector (op z x n)
    VToNat v -> vVector (genShift (V.zipWith . muxRValue) (op z) x (toWord v))
    _        -> panic $ unwords ["Verifier.SAW.Simulator.RME.shiftOp", show y]

-- BitBlast --

-- shift{L,R} :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> Vec n a;
shiftOp :: AIG.IsAIG l g => g s
        -> (BThunk (l s) -> Vector (BThunk (l s)) -> Int -> Vector (BThunk (l s)))
        -> (l s -> AIG.BV (l s) -> Int -> LitVector (l s))
        -> BValue (l s)
shiftOp be vecOp wordOp =
  constFun $
  constFun $
  VFun $ \x -> return $
  strictFun $ \xs -> return $
  strictFun $ \y -> do
    (n, f) <- case xs of
                VVector xv -> return (V.length xv, VVector . vecOp x xv)
                VWord xlv -> do l <- toBool <$> force x
                                return (AIG.length xlv, VWord . wordOp l xlv)
                _ -> panic $ "Verifier.SAW.Simulator.BitBlast.shiftOp: " ++ show xs
    case y of
      VNat i   -> return (f (fromInteger (i `min` toInteger n)))
      VToNat v -> do
        ilv <- toWord v
        AIG.muxInteger (lazyMux be (muxBVal be)) n ilv (return . f)
      _        -> panic $ "Verifier.SAW.Simulator.BitBlast.shiftOp: " ++ show y

---------------}

-- foldr :: (a b :: sort 0) -> (n :: Nat) -> (a -> b -> b) -> b -> Vec n a -> b;
foldrOp :: (VMonadLazy l, Show (Extra l)) => Unpack l -> Value l
foldrOp unpack =
  constFun $
  constFun $
  constFun $
  strictFun $ \f -> return $
  VFun $ \z -> return $
  strictFun $ \xs -> do
    let g x m = do fx <- apply f x
                   y <- delay m
                   apply fx y
    xv <- toVector unpack xs
    V.foldr g (force z) xv

-- op :: Integer -> Integer;
intUnOp :: VMonad l => String -> (VInt l -> MInt l) -> Value l
intUnOp nm f =
  intFun nm $ \x ->
  VInt <$> f x

-- op :: Integer -> Integer -> Integer;
intBinOp :: VMonad l => String -> (VInt l -> VInt l -> MInt l) -> Value l
intBinOp nm f =
  intFun (nm++" x") $ \x -> return $
  intFun (nm++" y") $ \y ->
  VInt <$> f x y

-- op :: Integer -> Integer -> Bool;
intBinCmp :: VMonad l =>
  String -> (VInt l -> VInt l -> MBool l) -> Value l
intBinCmp nm f =
  intFun (nm++" x") $ \x -> return $
  intFun (nm++" y") $ \y ->
  VBool <$> f x y

{-
-- primitive intAdd :: Integer -> Integer -> Integer;
intAddOp :: (VMonad l, VInt l ~ Integer) => Value l
intAddOp = intBinOp "intAdd" (+)

-- primitive intSub :: Integer -> Integer -> Integer;
intSubOp :: (VMonad l, VInt l ~ Integer) => Value l
intSubOp = intBinOp "intSub" (-)

-- primitive intMul :: Integer -> Integer -> Integer;
intMulOp :: (VMonad l, VInt l ~ Integer) => Value l
intMulOp = intBinOp "intMul" (*)

-- primitive intDiv :: Integer -> Integer -> Integer;
intDivOp :: (VMonad l, VInt l ~ Integer) => Value l
intDivOp = intBinOp "intDiv" div

-- primitive intMod :: Integer -> Integer -> Integer;
intModOp :: (VMonad l, VInt l ~ Integer) => Value l
intModOp = intBinOp "intMod" mod

-- primitive intMin :: Integer -> Integer -> Integer;
intMinOp :: (VMonad l, VInt l ~ Integer) => Value l
intMinOp = intBinOp "intMin" min

-- primitive intMax :: Integer -> Integer -> Integer;
intMaxOp :: (VMonad l, VInt l ~ Integer) => Value l
intMaxOp = intBinOp "intMax" max

-- primitive intNeg :: Integer -> Integer;
intNegOp :: (VMonad l, VInt l ~ Integer) => Value l
intNegOp = intUnOp "intNeg x" negate

-- primitive intEq  :: Integer -> Integer -> Bool;
intEqOp :: (VMonad l, VInt l ~ Integer) => (Bool -> VBool l) -> Value l
intEqOp = intBinCmp "intEq" (==)

-- primitive intLe  :: Integer -> Integer -> Bool;
intLeOp :: (VMonad l, VInt l ~ Integer) => (Bool -> VBool l) -> Value l
intLeOp = intBinCmp "intLe" (<=)

-- primitive intLt  :: Integer -> Integer -> Bool;
intLtOp :: (VMonad l, VInt l ~ Integer) => (Bool -> VBool l) -> Value l
intLtOp = intBinCmp "intLt" (<)
-}

-- primitive intToNat :: Integer -> Nat;
intToNatOp :: (VMonad l, VInt l ~ Integer) => Value l
intToNatOp =
  intFun "intToNat" $ \x -> return $!
    if x >= 0 then VNat (fromInteger x) else VNat 0

-- primitive natToInt :: Nat -> Integer;
natToIntOp :: (VMonad l, VInt l ~ Integer) => Value l
natToIntOp = natFun' "natToInt" $ \x -> return $ VInt (toInteger x)

-- primitive bvLg2 : (n : Nat) -> Vec n Bool -> Vec n Bool;
bvLg2Op :: VMonad l => (Value l -> MWord l) -> (VWord l -> MWord l) -> Value l
bvLg2Op asWord wordLg2 =
  natFun' "bvLg2 1" $ \_n -> return $
  strictFun $ \w -> (return . VWord) =<< (wordLg2 =<< asWord w)

-- primitive error :: (a :: sort 0) -> String -> a;
errorOp :: VMonad l => Value l
errorOp =
  constFun $
  strictFun $ \x ->
  case x of
    VString s -> Prim.userError (Text.unpack s)
    _ -> Prim.userError "unknown error"

------------------------------------------------------------
-- Conditionals

iteOp :: (VMonadLazy l, Show (Extra l)) => BasePrims l -> Value l
iteOp bp =
  constFun $
  strictFun $ \b -> return $
  VFun $ \x -> return $
  VFun $ \y -> lazyMuxValue bp (toBool b) (force x) (force y)

lazyMuxValue ::
  (VMonadLazy l, Show (Extra l)) =>
  BasePrims l -> VBool l -> MValue l -> MValue l -> MValue l
lazyMuxValue bp b x y =
  case bpAsBool bp b of
    Just True  -> x
    Just False -> y
    Nothing ->
      do x' <- x
         y' <- y
         muxValue bp b x' y'

muxValue :: forall l.
  (VMonadLazy l, Show (Extra l)) =>
  BasePrims l -> VBool l -> Value l -> Value l -> MValue l
muxValue bp b = value
  where
    value :: Value l -> Value l -> MValue l
    value (VFun f)          (VFun g)          = return $ VFun $ \a -> do
                                                  x <- f a
                                                  y <- g a
                                                  value x y
    value VUnit             VUnit             = return VUnit
    value (VPair x1 x2)     (VPair y1 y2)     = VPair <$> thunk x1 y1 <*> thunk x2 y2
    value (VRecordValue elems1) (VRecordValue
                                 (alistAllFields (map fst elems1) ->
                                  Just elems2)) =
      VRecordValue <$>
      zipWithM (\(f,th1) th2 -> (f,) <$> thunk th1 th2) elems1 elems2
    value (VCtorApp i xv)   (VCtorApp j yv)   | i == j = VCtorApp i <$> thunks xv yv
    value (VVector xv)      (VVector yv)      = VVector <$> thunks xv yv
    value (VBool x)         (VBool y)         = VBool <$> bpMuxBool bp b x y
    value (VWord x)         (VWord y)         = VWord <$> bpMuxWord bp b x y
    value (VInt x)          (VInt y)          = VInt <$> bpMuxInt bp b x y
    value (VIntMod n x)     (VIntMod _ y)     = VIntMod n <$> bpMuxInt bp b x y
    value (VNat m)          (VNat n)          | m == n = return $ VNat m
    value (VString x)       (VString y)       | x == y = return $ VString x
    value (VFloat x)        (VFloat y)        | x == y = return $ VFloat x
    value (VDouble x)       (VDouble y)       | x == y = return $ VDouble y
    value (VExtra x)        (VExtra y)        = VExtra <$> bpMuxExtra bp b x y
    value x@(VWord _)       y                 = toVector (bpUnpack bp) x >>= \xv -> value (VVector xv) y
    value x                 y@(VWord _)       = toVector (bpUnpack bp) y >>= \yv -> value x (VVector yv)
    value x@(VNat _)        y                 = nat x y
    value x@(VBVToNat _ _)  y                 = nat x y
    value x@(VIntToNat _)   y                 = nat x y
    value (TValue x)        (TValue y)        = TValue <$> tvalue x y
    value x                 y                 =
      panic $ "Verifier.SAW.Simulator.Prims.iteOp: malformed arguments: "
      ++ show x ++ " " ++ show y

    tvalue :: TValue l -> TValue l -> EvalM l (TValue l)
    tvalue (VSort x)         (VSort y)         | x == y = return $ VSort y
    tvalue x                 y                 =
      panic $ "Verifier.SAW.Simulator.Prims.iteOp: malformed arguments: "
      ++ show x ++ " " ++ show y

    thunks :: Vector (Thunk l) -> Vector (Thunk l) -> EvalM l (Vector (Thunk l))
    thunks xv yv
      | V.length xv == V.length yv = V.zipWithM thunk xv yv
      | otherwise                  = panic "Verifier.SAW.Simulator.Prims.iteOp: malformed arguments"

    thunk :: Thunk l -> Thunk l -> EvalM l (Thunk l)
    thunk x y = delay $ do x' <- force x; y' <- force y; value x' y'

    nat :: Value l -> Value l -> MValue l
    nat v1 v2 =
      do let w = toInteger (max (natSize bp v1) (natSize bp v2))
         unless (w <= toInteger (maxBound :: Int))
                (panic "muxValue" ["width too large", show w])
         x1 <- natToWord bp (fromInteger w) v1
         x2 <- natToWord bp (fromInteger w) v2
         VBVToNat (fromInteger w) . VWord <$> bpMuxWord bp b x1 x2

-- fix :: (a :: sort 0) -> (a -> a) -> a;
fixOp :: (VMonadLazy l, MonadFix (EvalM l), Show (Extra l)) => Value l
fixOp =
  constFun $
  strictFun $ \f ->
  force =<< mfix (\x -> delay (apply f x))

------------------------------------------------------------
-- SMT Array

-- Array :: sort 0 -> sort 0 -> sort 0
arrayTypeOp :: VMonad l => Value l
arrayTypeOp = pureFun $ \a -> pureFun $ \b -> TValue (VArrayType (toTValue a) (toTValue b))

-- arrayConstant :: (a b :: sort 0) -> b -> (Array a b);
arrayConstantOp :: VMonad l => BasePrims l -> Value l
arrayConstantOp bp =
  pureFun $ \a ->
  constFun $
  strictFun $ \e ->
    VArray <$> (bpArrayConstant bp) (toTValue a) e

-- arrayLookup :: (a b :: sort 0) -> (Array a b) -> a -> b;
arrayLookupOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
arrayLookupOp bp =
  constFun $
  constFun $
  pureFun $ \f ->
  strictFun $ \i -> do
    f' <- toArray f
    (bpArrayLookup bp) f' i

-- arrayUpdate :: (a b :: sort 0) -> (Array a b) -> a -> b -> (Array a b);
arrayUpdateOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
arrayUpdateOp bp =
  constFun $
  constFun $
  pureFun $ \f ->
  pureFun $ \i ->
  strictFun $ \e -> do
    f' <- toArray f
    VArray <$> (bpArrayUpdate bp) f' i e

-- arrayEq : (a b : sort 0) -> (Array a b) -> (Array a b) -> Bool;
arrayEqOp :: (VMonad l, Show (Extra l)) => BasePrims l -> Value l
arrayEqOp bp =
  constFun $
  constFun $
  pureFun $ \x ->
  strictFun $ \y -> do
    x' <- toArray x
    y' <- toArray y
    VBool <$> bpArrayEq bp x' y'
