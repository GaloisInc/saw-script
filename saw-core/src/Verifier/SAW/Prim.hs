{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}

{- |
Module      : Verifier.SAW.Prim
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Prim where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import qualified Control.Exception as X
import Data.Bits
import Data.Typeable (Typeable)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Numeric.Natural (Natural)

------------------------------------------------------------
-- Natural numbers

-- | width(n) = 1 + floor(log_2(n))
widthNat :: Natural -> Natural
widthNat 0 = 0
widthNat n = 1 + widthNat (n `div` 2)

-- data Vec :: (n :: Nat) -> sort 0 -> sort 0
data Vec t a = Vec t !(Vector a)

------------------------------------------------------------
-- Unsigned, variable-width bit vectors

data BitVector = BV { width :: !Int, unsigned :: !Integer }
    deriving Show
-- ^ Invariant: BV w x requires that 0 <= x < 2^w.

bitMask :: Int -> Integer
bitMask w = bit w - 1

-- | Smart constructor for bitvectors.
bv :: Int -> Integer -> BitVector
bv w x = BV w (x .&. bitMask w)

signed :: BitVector -> Integer
signed (BV w x)
  | w > 0 && testBit x (w - 1) = x - bit w
  | otherwise                  = x

bvAt :: BitVector -> Int -> Bool
bvAt (BV w x) i = testBit x (w - 1 - i)

-- | Conversion from list of bits to integer (big-endian)
bvToInteger :: Vector Bool -> Integer
bvToInteger = V.foldl' (\x b -> if b then 2*x+1 else 2*x) 0

unpackBitVector :: BitVector -> Vector Bool
unpackBitVector x = V.generate (width x) (bvAt x)

packBitVector :: Vector Bool -> BitVector
packBitVector v = BV (V.length v) (bvToInteger v)

------------------------------------------------------------
-- Primitive operations

-- coerce :: (y x :: sort 0) -> Eq (sort 0) x y -> x -> y;
coerce :: () -> () -> () -> a -> a
coerce _ _ _ x = x

-- ite :: ?(a :: sort 1) -> Bool -> a -> a -> a;
ite :: t -> Bool -> a -> a -> a
ite _ b x y = if b then x else y

-- Succ :: Nat -> Nat;
succNat :: Integer -> Integer
succNat = succ

-- addNat :: Nat -> Nat -> Nat;
addNat :: Integer -> Integer -> Integer
addNat = (+)

-- get :: (n :: Nat) -> (e :: sort 0) -> Vec n e -> Fin n -> e;
--get :: Int -> t -> Vec t e -> Fin -> e
--get _ _ (Vec _ v) i = v ! fromEnum i

-- append :: (m n :: Nat) -> (e :: sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
append :: Int -> Int -> t -> Vec t e -> Vec t e -> Vec t e
append _ _ _ (Vec t xv) (Vec _ yv) = Vec t ((V.++) xv yv)

-- at :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a;
at :: Int -> t -> Vec t e -> Int -> e
at _ _ (Vec _ v) i = v ! i

-- atWithDefault :: (n :: Nat) -> (a :: sort 0) -> a -> Vec n a -> Nat -> a;
atWithDefault :: Int -> t -> e -> Vec t e -> Int -> e
atWithDefault _ _ z (Vec _ v) i
  | i < V.length v = v ! i
  | otherwise = z

-- upd :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a -> Vec n a;
upd :: Int -> t -> Vec t e -> Int -> e -> Vec t e
upd _ _ (Vec t v) i e = Vec t (v V.// [(i, e)])

(!) :: Vector a -> Int -> a
(!) v i = case v V.!? i of
  Just x -> x
  Nothing -> invalidIndex (toInteger i)

----------------------------------------
-- Bitvector operations

-- bvNat : (n : Nat) -> Nat -> Vec n Bool;
bvNat :: Int -> Integer -> BitVector
bvNat w x = bv w x

-- bvAdd : (n : Nat) -> Vec n Bool -> Vec n Bool -> Vec n Bool;
bvAdd, bvSub, bvMul :: Natural -> BitVector -> BitVector -> BitVector
bvAdd _ (BV w x) (BV _ y) = bv w (x + y)
bvSub _ (BV w x) (BV _ y) = bv w (x - y)
bvMul _ (BV w x) (BV _ y) = bv w (x * y)

bvNeg :: Natural -> BitVector -> BitVector
bvNeg _ x@(BV w _) = bv w $ negate $ signed x

bvAnd, bvOr, bvXor :: Int -> BitVector -> BitVector -> BitVector
bvAnd _ (BV w x) (BV _ y) = BV w (x .&. y)
bvOr  _ (BV w x) (BV _ y) = BV w (x .|. y)
bvXor _ (BV w x) (BV _ y) = BV w (x `xor` y)

bvNot :: Int -> BitVector -> BitVector
bvNot _ (BV w x) = BV w (x `xor` bitMask w)

bvEq, bvult, bvule, bvugt, bvuge, bvsgt, bvsge, bvslt, bvsle
    :: Int -> BitVector -> BitVector -> Bool
bvEq  _ x y = unsigned x == unsigned y
bvugt _ x y = unsigned x >  unsigned y
bvuge _ x y = unsigned x >= unsigned y
bvult _ x y = unsigned x <  unsigned y
bvule _ x y = unsigned x <= unsigned y
bvsgt _ x y = signed x >  signed y
bvsge _ x y = signed x >= signed y
bvslt _ x y = signed x <  signed y
bvsle _ x y = signed x <= signed y

bvPopcount :: Int -> BitVector -> BitVector
bvPopcount _ (BV w x) = BV w (toInteger (popCount x))

bvCountLeadingZeros :: Int -> BitVector -> BitVector
bvCountLeadingZeros _ (BV w x) = BV w (toInteger (go 0))
 where
 go !i
   | i < w && testBit x (w - i - 1) == False = go (i+1)
   | otherwise = i

bvCountTrailingZeros :: Int -> BitVector -> BitVector
bvCountTrailingZeros _ (BV w x) = BV w (toInteger (go 0))
 where
 go !i
   | i < w && testBit x i == False = go (i+1)
   | otherwise = i

-- | @get@ specialized to BitVector (big-endian)
-- get :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a;
--get_bv :: Int -> () -> BitVector -> Fin -> Bool
--get_bv _ _ x i = testBit (unsigned x) (width x - 1 - fromEnum i)
-- little-endian version:
-- get_bv _ _ x i = testBit (unsigned x) (fromEnum i)

-- | @at@ specialized to BitVector (big-endian)
-- at :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a;
at_bv :: Int -> () -> BitVector -> Natural -> Bool
at_bv _ _ x i = testBit (unsigned x) (width x - 1 - fromIntegral i)

-- | @set@ specialized to BitVector (big-endian)
-- set :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a -> Vec n a;
--set_bv :: Int -> () -> BitVector -> Fin -> Bool -> BitVector
--set_bv _ _ x i b = BV (width x) $ f (unsigned x) (width x - 1 - fromEnum i)
--  where f = if b then setBit else clearBit

-- | @append@ specialized to BitVector (big-endian)
-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
append_bv :: Int -> Int -> () -> BitVector -> BitVector -> BitVector
append_bv _ _ _ (BV m x) (BV n y) = BV (m + n) (shiftL x n .|. y)
-- little-endian version:
-- append_bv _ _ _ (BV m x) (BV n y) = BV (m + n) (x .|. shiftL y m)

-- bvToNat : (n : Nat) -> Vec n Bool -> Nat;
bvToNat :: Int -> BitVector -> Integer
bvToNat _ (BV _ x) = x

-- bvAddWithCarry : (n : Nat) -> Vec n Bool -> Vec n Bool -> Bool * Vec n Bool;
bvAddWithCarry :: Int -> BitVector -> BitVector -> (Bool, BitVector)
bvAddWithCarry _ (BV w x) (BV _ y) = (testBit z w, bv w z)
    where z = x + y

bvUDiv :: Int -> BitVector -> BitVector -> Maybe BitVector
bvUDiv _ (BV w x) (BV _ y)
  | y == 0    = Nothing
  | otherwise = Just (bv w (x `quot` y))

bvURem :: Int -> BitVector -> BitVector -> Maybe BitVector
bvURem _ (BV w x) (BV _ y)
  | y == 0    = Nothing
  | otherwise = Just (bv w (x `rem` y))

bvSDiv :: Int -> BitVector -> BitVector -> Maybe BitVector
bvSDiv _ x y
  | unsigned y == 0 = Nothing
  | otherwise       = Just (bv (width x) (signed x `quot` signed y))

bvSRem :: Int -> BitVector -> BitVector -> Maybe BitVector
bvSRem _ x y
  | unsigned y == 0 = Nothing
  | otherwise       = Just (bv (width x) (signed x `rem` signed y))

bvShl :: Int -> BitVector -> Int -> BitVector
bvShl _ (BV w x) i = bv w (x `shiftL` i)

bvShr :: Int -> BitVector -> Int -> BitVector
bvShr _ (BV w x) i = bv w (x `shiftR` i)

bvSShr :: Int -> BitVector -> Int -> BitVector
bvSShr _ x i = bv (width x) (signed x `shiftR` i)

-- bvTrunc : (m n : Nat) -> Vec (addNat m n) Bool -> Vec n Bool;
bvTrunc :: Int -> Int -> BitVector -> BitVector
bvTrunc _ n (BV _ x) = bv n x

-- bvUExt : (m n : Nat) -> Vec n Bool -> Vec (addNat m n) Bool;
bvUExt :: Int -> Int -> BitVector -> BitVector
bvUExt m n x = BV (m + n) (unsigned x)

-- bvSExt : (m n : Nat) -> Vec (Succ n) Bool -> Vec (addNat m (Succ n)) Bool;
bvSExt :: Int -> Int -> BitVector -> BitVector
bvSExt m n x = bv (m + n + 1) (signed x)

-- | @take@ specialized to BitVector (big-endian)
-- take :: (a :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) a -> Vec m a;
take_bv :: () -> Int -> Int -> BitVector -> BitVector
take_bv _ m n (BV _ x) = bv m (x `shiftR` n)
-- little-endian version:
-- take_bv _ m _ (BV _ x) = bv m x

-- | @vDrop@ specialized to BitVector (big-endian)
-- drop :: (a :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) a -> Vec n a;
drop_bv :: () -> Int -> Int -> BitVector -> BitVector
drop_bv _ _ n (BV _ x) = bv n x
-- little-endian version:
-- drop_bv _ m n (BV _ x) = BV n (x `shiftR` m)

-- | @slice@ specialized to BitVector
slice_bv :: () -> Int -> Int -> Int -> BitVector -> BitVector
slice_bv _ _ n o (BV _ x) = bv n (shiftR x o)
-- little-endian version:
-- slice_bv _ i n _ (BV _ x) = bv n (shiftR x i)

------------------------------------------------------------
-- Base 2 logarithm

bvLg2 :: BitVector -> BitVector
bvLg2 (BV m x) = BV m (if d > 0 then k+1 else k)
  where (k, d) = lg2rem x

-- | lg2rem n = (k, d) <--> n = 2^k + d, with d < 2^k.
lg2rem :: Integer -> (Integer, Integer)
lg2rem 0 = (0, -1)
lg2rem 1 = (0, 0)
lg2rem n = (k+1, 2*d+r)
  where (q, r) = n `divMod` 2
        (k, d) = lg2rem q

------------------------------------------------------------
-- BitVector shift/rotate

bvRotateL :: BitVector -> Integer -> BitVector
bvRotateL (BV w x) i = bv w ((x `shiftL` j) .|. (x `shiftR` (w - j)))
  where j = fromInteger (i `mod` toInteger w)

bvRotateR :: BitVector -> Integer -> BitVector
bvRotateR w i = bvRotateL w (- i)

bvShiftL ::
  Bool {- ^ bit value to shift in -} ->
  BitVector {- ^ value to shift -} ->
  Integer {- ^ amount to shift by -} ->
  BitVector
bvShiftL c (BV w x) i = bv w ((x `shiftL` j) .|. c')
  where c' = if c then (1 `shiftL` j) - 1 else 0
        j = fromInteger (i `min` toInteger w)

bvShiftR ::
  Bool {- ^ bit value to shift in -} ->
  BitVector {- ^ value to shift -} ->
  Integer {- ^ amount to shift by -} ->
  BitVector
bvShiftR c (BV w x) i = bv w (c' .|. (x `shiftR` j))
  where c' = if c then (full `shiftL` (w - j)) .&. full else 0
        full = (1 `shiftL` w) - 1
        j = fromInteger (i `min` toInteger w)


----------------------------------------
-- Errors

data EvalError
  = InvalidIndex Integer
  | DivideByZero
  | UnsupportedPrimitive String String
  | UserError String
  deriving (Eq, Typeable)

instance X.Exception EvalError

instance Show EvalError where
  show e = case e of
    InvalidIndex i -> "invalid sequence index: " ++ show i
    DivideByZero -> "division by 0"
    UnsupportedPrimitive b p -> "unsupported primitive " ++ p ++ " in " ++ b ++ " backend"
    UserError msg -> "Run-time error: " ++ msg

-- | A sequencing operation has gotten an invalid index.
invalidIndex :: Integer -> a
invalidIndex i = X.throw (InvalidIndex i)

-- | For division by 0.
divideByZero :: a
divideByZero = X.throw DivideByZero

-- | A backend with a unsupported primitive.
unsupportedPrimitive :: String -> String -> a
unsupportedPrimitive backend primitive =
  X.throw $ UnsupportedPrimitive backend primitive

-- | For `error`
userError :: String -> a
userError msg = X.throw (UserError msg)

-- | Convert asynchronous EvalError exceptions into IO exceptions.
rethrowEvalError :: IO a -> IO a
rethrowEvalError m = run `X.catch` rethrow
  where
    run = do
      a <- m
      return $! a

    rethrow :: EvalError -> IO a
    rethrow exn = fail (show exn) -- X.throwIO (EvalError exn)
