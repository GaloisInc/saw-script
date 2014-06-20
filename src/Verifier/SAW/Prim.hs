{-# LANGUAGE CPP #-}
module Verifier.SAW.Prim where

import Control.Applicative
import Control.Exception (assert)
import Data.Bits
import Data.Vector ( Vector )
import qualified Data.Vector as V

------------------------------------------------------------
-- Natural numbers

-- | A natural number.
newtype Nat = Nat { unNat :: Integer }
  deriving (Eq,Ord)

instance Show Nat where
  show (Nat x) = show x

instance Num Nat where
  Nat x + Nat y = Nat (x + y)
  Nat x * Nat y = Nat (x * y)
  Nat x - Nat y | r >= 0 = Nat r
                | otherwise = error "internal: Nat subtraction result must be non-negative."
    where r = x - y

  negate (Nat 0) = Nat 0
  negate _ = error "Nat negation is upsupported."

  abs = id

  signum (Nat 0) = 0
  signum (Nat _) = 1

  fromInteger r | r >= 0 = Nat r
                | otherwise = error "internal: Natural numbers must be non-negative."

instance Enum Nat where
  succ (Nat x) = Nat (succ x)
  pred (Nat 0) = error "Nat 0 has no predecessor."
  pred (Nat x) = Nat (pred x)

  toEnum   = fromIntegral
  fromEnum = fromIntegral

  enumFrom       (Nat x)                 = Nat <$> enumFrom x
  enumFromThen   (Nat x) (Nat y)         = Nat <$> enumFromThen x y
  enumFromTo     (Nat x)         (Nat z) = Nat <$> enumFromTo x z
  enumFromThenTo (Nat x) (Nat y) (Nat z) = Nat <$> enumFromThenTo x y z


instance Real Nat where
  toRational (Nat x) = toRational x

instance Integral Nat where
  Nat x `quotRem` Nat y | y == 0 = error "Nat division by zero."
                        | otherwise = (Nat q, Nat r)
    where (q,r) = x `quotRem` y
  divMod = quotRem
  toInteger (Nat x) = x  

instance Bits Nat where
  Nat x .&. Nat y   = Nat (x .&. y)
  Nat x .|. Nat y   = Nat (x .|. y)
  Nat x `xor` Nat y = Nat (x `xor` y)

  complement = error "complement(Nat) unsupported."
  Nat x `shift` i = Nat (x `shift` i)

  rotate = shift

  bit = Nat . bit
  Nat x `setBit` i = Nat (x `setBit` i)

  Nat x `clearBit` i = Nat (x `clearBit` i)

  complementBit (Nat x) i = Nat (x `complementBit` i)

  testBit (Nat x) i = testBit x i

  bitSize = error "bitSize(Nat) unsupported."

  isSigned _ = False

#if MIN_VERSION_base(4,6,0)
  popCount (Nat x) = popCount x
#endif

-- | width(n) = 1 + floor(log_2(n))
widthNat :: Nat -> Nat
widthNat 0 = 0
widthNat n = 1 + widthNat (n `div` 2)

------------------------------------------------------------
-- Finite indices

data Fin = FinVal { finVal :: !Nat, finRem :: Nat }
    deriving (Eq, Show)

finFromBound :: Nat -> Nat -> Fin
finFromBound i n
  | i < n = FinVal i (pred (n - i))
  | otherwise = error "finFromBound given out-of-range index."
                                                                                  
finSize :: Fin -> Nat
finSize (FinVal x r) = succ (r + x)

incFinBy :: Fin -> Nat -> Maybe Fin
incFinBy x y
   | r' < 0 = Nothing
   | otherwise = Just x'
 where r' = toInteger (finRem x) - toInteger y
       x' = FinVal (finVal x + y) (fromInteger r')

-- finDivMod :: (m n :: Nat) -> Fin (mulNat m n) -> #(Fin m, Fin n);
finDivMod :: Nat -> Nat -> Fin -> (Fin, Fin)
finDivMod _ n (FinVal v r) = (FinVal v1 r1, FinVal v2 r2)
  where (v1, v2) = divMod v n
        (r1, r2) = divMod r n

instance Enum Fin where
  succ (FinVal _ 0) = error "FinVal has no successor."
  succ (FinVal x r) = FinVal (succ x) (pred r)
  pred (FinVal 0 _) = error "FinVal has no predecessor."
  pred (FinVal x r) = FinVal (pred x) (succ r)
  toEnum x = FinVal (toEnum x) (error "FinVal.toEnum has no bound.")
  fromEnum = fromEnum . finVal
  enumFrom x | finRem x == 0 = [x]
             | otherwise = x : enumFrom (succ x)

  enumFromThen x y =
    case incFinBy x (finVal y) of
      Nothing -> [x]
      Just x' -> x : enumFromThen x' y
 
  enumFromTo x z = enumFromThenTo x (FinVal 1 (finSize x)) z

  enumFromThenTo x0 y z =
      assert (finSize x0 == finSize z) $
      assert (finVal x0 <= finVal z) $
      go x0
    where go x = case incFinBy x (finVal y) of
                   Nothing -> [x]
                   Just x' -> x : go x'

natSplitFin :: Nat -> Nat -> Either Fin Nat
natSplitFin n i
  | i < n = Left (FinVal i (pred (n - i)))
  | otherwise = Right (i - n)

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

-- finInc :: (i n :: Nat) -> Fin n -> Fin (addNat i n);
finInc :: Nat -> Nat -> Fin -> Fin
finInc i _n (FinVal l r) = FinVal (i + l) r
  -- ^ Precondition: n == l + r + 1

-- finIncLim :: (n :: Nat) -> (m :: Nat) -> Fin m -> Fin (addNat m n);
finIncLim :: Nat -> Nat -> Fin -> Fin
finIncLim n _m (FinVal l r) = FinVal l (r + n)
  -- ^ Precondition: m == l + r + 1

-- finMax :: (n :: Nat) -> Maybe (Fin n);
finMax :: Nat -> Maybe Fin
finMax n = if n == 0 then Nothing else Just (FinVal (n - 1) 0)

-- finPred :: (n :: Nat) -> Fin n -> Maybe (Fin n);
finPred :: Nat -> Fin -> Maybe Fin
finPred _ (FinVal l r) = if l == 0 then Nothing else Just (FinVal (l - 1) (r + 1))

-- generate :: (n :: Nat) -> (e :: sort 0) -> (Fin n -> e) -> Vec n e;
generate :: Nat -> () -> (Fin -> a) -> Vector a
generate n _ f = V.generate (fromEnum n) (\i -> f (finFromBound (fromIntegral i) n))

-- get :: (n :: Nat) -> (e :: sort 0) -> Vec n e -> Fin n -> e;
get :: Int -> t -> Vec t e -> Fin -> e
get _ _ (Vec _ v) i = v V.! fromEnum i

-- append :: (m n :: Nat) -> (e :: sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
append :: Int -> Int -> t -> Vec t e -> Vec t e -> Vec t e
append _ _ _ (Vec t xv) (Vec _ yv) = Vec t ((V.++) xv yv)


----------------------------------------
-- Bitvector operations

-- bvNat :: (x :: Nat) -> Nat -> bitvector x;
bvNat :: Int -> Integer -> BitVector
bvNat w x = bv w x

-- bvAdd :: (x :: Nat) -> bitvector x -> bitvector x -> bitvector x;
bvAdd, bvSub, bvMul :: Nat -> BitVector -> BitVector -> BitVector
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

-- | @get@ specialized to BitVector (big-endian)
-- get :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Fin n -> a;
get_bv :: Int -> () -> BitVector -> Fin -> Bool
get_bv _ _ x i = testBit (unsigned x) (width x - 1 - fromEnum i)
-- little-endian version:
-- get_bv _ _ x i = testBit (unsigned x) (fromEnum i)

-- | @append@ specialized to BitVector (big-endian)
-- append :: (m n :: Nat) -> (a :: sort 0) -> Vec m a -> Vec n a -> Vec (addNat m n) a;
append_bv :: Int -> Int -> () -> BitVector -> BitVector -> BitVector
append_bv _ _ _ (BV m x) (BV n y) = BV (m + n) (shiftL x n .|. y)
-- little-endian version:
-- append_bv _ _ _ (BV m x) (BV n y) = BV (m + n) (x .|. shiftL y m)

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
bvMbit _ (BV _ x) i = testBit x (fromEnum i)

-- bvTrunc :: (x y :: Nat) -> bitvector (addNat y x) -> bitvector y;
bvTrunc :: Int -> Int -> BitVector -> BitVector
bvTrunc _ n (BV _ x) = bv n x

-- bvUExt :: (x y :: Nat) -> bitvector y -> bitvector (addNat y x);
bvUExt :: Int -> Int -> BitVector -> BitVector
bvUExt m n x = BV (m + n) (unsigned x)

-- bvSExt :: (x y :: Nat) -> bitvector (Succ y) -> bitvector (addNat (Succ y) x);
bvSExt :: Int -> Int -> BitVector -> BitVector
bvSExt m n x = bv (m + n + 1) (signed x)

-- | @vTake@ specialized to BitVector (big-endian)
-- vTake :: (a :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) a -> Vec m a;
vTake_bv :: () -> Int -> Int -> BitVector -> BitVector
vTake_bv _ m n (BV _ x) = bv m (x `shiftR` n)
-- little-endian version:
-- vTake_bv _ m _ (BV _ x) = bv m x

-- | @vDrop@ specialized to BitVector (big-endian)
-- vDrop :: (a :: sort 0) -> (m n :: Nat) -> Vec (addNat m n) a -> Vec n a;
vDrop_bv :: () -> Int -> Int -> BitVector -> BitVector
vDrop_bv _ _ n (BV _ x) = bv n x
-- little-endian version:
-- vDrop_bv _ m n (BV _ x) = BV n (x `shiftR` m)

-- | @slice@ specialized to BitVector
slice_bv :: () -> Int -> Int -> Int -> BitVector -> BitVector
slice_bv _ _ n o (BV _ x) = bv n (shiftR x o)
-- little-endian version:
-- slice_bv _ i n _ (BV _ x) = bv n (shiftR x i)

------------------------------------------------------------
-- Bitvectors polynomial operations

-- | Polynomial GF(2) multiplication for type Nat
pMulNat :: Nat -> Nat -> Nat
pMulNat 0 y = 0
pMulNat x y = if odd x then r `xor` y else r
  where r = pMulNat (x `shiftR` 1) y `shiftL` 1

pDivModNat :: Nat -> Nat -> (Nat, Nat)
pDivModNat x 0 = (0, x) -- In Cryptol, this case is undefined.
pDivModNat x y = (qr `shiftR` ySize, qr .&. (bit ySize - 1))
  where
    xSize = fromIntegral (widthNat x) - 1
    ySize = fromIntegral (widthNat y) - 1
    mask = y `clearBit` ySize
    qr = go xSize x
    go i z
      | i < ySize     = z
      | z `testBit` i = go (i - 1) (z `xor` (mask `shiftL` (i - ySize)))
      | otherwise     = go (i - 1) z

bvPMul :: Nat -> Nat -> BitVector -> BitVector -> BitVector
bvPMul _ _ (BV m x) (BV n y) = BV w (unNat (pMulNat (Nat x) (Nat y)))
  where w = max 0 (m + n - 1)

bvPDiv :: Nat -> Nat -> BitVector -> BitVector -> BitVector
bvPDiv _ _ (BV m x) (BV _ y) = BV m (unNat (fst (pDivModNat (Nat x) (Nat y))))

bvPMod :: Nat -> Nat -> BitVector -> BitVector -> BitVector
bvPMod _ _ (BV _ x) (BV n y) = BV (n - 1) (unNat (snd (pDivModNat (Nat x) (Nat y))))
