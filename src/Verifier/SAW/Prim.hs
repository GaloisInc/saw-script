module Verifier.SAW.Prim where

import Data.Bits
import Data.Vector ( Vector )
import qualified Data.Vector as V

------------------------------------------------------------
-- Primitive types

-- data Fin :: (n :: Nat) -> sort 0 where {
--     FinVal :: (x r :: Nat) -> Fin (Succ (addNat r x));
--   }
data Fin = FinVal !Int !Int
    deriving Show

-- data Vec :: (n :: Nat) -> sort 0 -> sort 0
data Vec t a = Vec t !(Vector a)

-- bitvector :: (n :: Nat) -> sort 0;
-- bitvector n = Vec n Bool;
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

------------------------------------------------------------
-- Primitive operations

-- ite :: ?(a :: sort 1) -> Bool -> a -> a -> a;
ite :: t -> Bool -> a -> a -> a
ite _ b x y = if b then x else y

-- Succ :: Nat -> Nat;
succNat :: Integer -> Integer
succNat = succ

-- addNat :: Nat -> Nat -> Nat;
addNat :: Integer -> Integer -> Integer
addNat = (+)

-- finInc :: (i n :: Nat) -> Fin n -> Fin (addNat i n);
-- FIXME: Is this really necessary?
finInc :: Int -> Int -> Fin -> Fin
finInc i _n (FinVal l r) = FinVal (i + l) r
  -- ^ Precondition: n == l + r + 1

-- finIncLim :: (n :: Nat) -> (m :: Nat) -> Fin m -> Fin (addNat m n);
-- FIXME: Is this really necessary?
finIncLim :: Int -> Int -> Fin -> Fin
finIncLim n _m (FinVal l r) = FinVal l (r + n)
  -- ^ Precondition: m == l + r + 1

-- get :: (n :: Nat) -> (e :: sort 0) -> Vec n e -> Fin n -> e;
get :: Int -> t -> Vec t e -> Fin -> e
get _ _ (Vec _ v) (FinVal i _) = (V.!) v i

-- append :: (m n :: Nat) -> (e :: sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
append :: Int -> Int -> t -> Vec t e -> Vec t e -> Vec t e
append _ _ _ (Vec t xv) (Vec _ yv) = Vec t ((V.++) xv yv)


----------------------------------------
-- Bitvector operations

-- bvNat :: (x :: Nat) -> Nat -> bitvector x;
bvNat :: Int -> Integer -> BitVector
bvNat w x = bv w x

-- bvAdd :: (x :: Nat) -> bitvector x -> bitvector x -> bitvector x;
bvAdd, bvSub, bvMul :: Int -> BitVector -> BitVector -> BitVector
bvAdd _ (BV w x) (BV _ y) = bv w (x + y)
bvSub _ (BV w x) (BV _ y) = bv w (x - y)
bvMul _ (BV w x) (BV _ y) = bv w (x * y)

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

-- | @get@ specialized to BitVector
-- get :: (n :: Nat) -> (e :: sort 0) -> Vec n e -> Fin n -> e;
get_bv :: Int -> () -> BitVector -> Fin -> Bool
get_bv _ _ x (FinVal i _) = testBit (unsigned x) i
-- ^ Assuming little-endian order

-- | @append@ specialized to BitVector
-- append :: (m n :: Nat) -> (e :: sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
append_bv :: Int -> Int -> () -> BitVector -> BitVector -> BitVector
append_bv _ _ _ (BV m x) (BV n y) = BV (m + n) (x .|. shiftL y m)
  -- ^ Assuming little-endian order

-- bvToNat :: (n :: Nat) -> bitvector n -> Nat;
bvToNat :: Int -> BitVector -> Integer
bvToNat _ (BV _ x) = x

-- bvAddWithCarry :: (x :: Nat) -> bitvector x -> bitvector x -> #(Bool, bitvector x);
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

-- bvMbit :: (n :: Nat) -> bitvector n -> Fin n -> Bool;
bvMbit :: Int -> BitVector -> Fin -> Bool
bvMbit _ (BV _ x) (FinVal i _) = testBit x i

-- bvTrunc :: (x y :: Nat) -> bitvector (addNat y x) -> bitvector y;
bvTrunc :: Int -> Int -> BitVector -> BitVector
bvTrunc _ n (BV _ x) = bv n x

-- bvUExt :: (x y :: Nat) -> bitvector y -> bitvector (addNat y x);
bvUExt :: Int -> Int -> BitVector -> BitVector
bvUExt m n x = BV (m + n) (unsigned x)

-- bvSExt :: (x y :: Nat) -> bitvector (Succ y) -> bitvector (addNat (Succ y) x);
bvSExt :: Int -> Int -> BitVector -> BitVector
bvSExt m n x = bv (m + n + 1) (signed x)

-- vTake :: (e :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) e -> Vec m e;
vTake_bv :: () -> Int -> Int -> BitVector -> BitVector
vTake_bv _ m _ (BV _ x) = bv m x
  -- ^ Assumes little-endian order

-- vDrop :: (e :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) e -> Vec n e;
vDrop_bv :: () -> Int -> Int -> BitVector -> BitVector
vDrop_bv _ m n (BV _ x) = BV n (x `shiftR` m)
  -- ^ Assumes little-endian order

-- | @slice@ specialized to BitVector
slice_bv :: () -> Int -> Int -> Int -> BitVector -> BitVector
slice_bv _ i n _ (BV _ x) = BV n (shiftR x i .&. bitMask n)
  -- ^ Assuming little-endian order
