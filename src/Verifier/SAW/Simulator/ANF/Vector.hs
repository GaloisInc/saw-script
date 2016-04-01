{- |
Module      : Verifier.SAW.Simulator.ANF.Vector
Copyright   : Galois, Inc. 2016
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : portable

Operations on big-endian vectors of ANF formulas.
-}

module Verifier.SAW.Simulator.ANF.Vector
  ( eq, ule, ult, sle, slt
  , neg, add, sub, mul
  , udiv, urem, sdiv, srem
  , pmul, pmod, pdiv
  , integer
  ) where

import Verifier.SAW.Simulator.ANF.Base (ANF)
import qualified Verifier.SAW.Simulator.ANF.Base as ANF

import Data.Bits
import Data.Vector (Vector)
import qualified Data.Vector as V

type ANFV = Vector ANF

-- | Constant integer literals
integer :: Int -> Integer -> ANFV
integer width x = V.reverse (V.generate width (ANF.constant . testBit x))

-- | Bitvector equality
eq :: ANFV -> ANFV -> ANF
eq x y = V.foldr ANF.conj ANF.true (V.zipWith ANF.iff x y)

-- | Unsigned less-than-or-equal
ule :: ANFV -> ANFV -> ANF
ule xv yv = go (V.toList xv) (V.toList yv)
  where
    go (x : xs) (y : ys) =
      let z = go xs ys
      in ANF.xor (ANF.conj y z) (ANF.conj (ANF.compl x) (ANF.xor y z))
    go _ _ = ANF.true

-- | Unsigned less-than
ult :: ANFV -> ANFV -> ANF
ult x y = ANF.compl (ule y x)

swap_sign :: ANFV -> ANFV
swap_sign x
  | V.null x = x
  | otherwise = V.singleton (ANF.compl (V.head x)) V.++ V.tail x

-- | Signed less-than-or-equal
sle :: ANFV -> ANFV -> ANF
sle x y = ule (swap_sign x) (swap_sign y)

-- | Signed less-than
slt :: ANFV -> ANFV -> ANF
slt x y = ult (swap_sign x) (swap_sign y)

-- | Big-endian bitvector increment with carry
increment :: [ANF] -> (ANF, [ANF])
increment [] = (ANF.true, [])
increment (x : xs) = (ANF.conj x c, ANF.xor x c : ys)
  where (c, ys) = increment xs

-- | Two's complement bitvector negation
neg :: ANFV -> ANFV
neg x = V.fromList (snd (increment (map ANF.compl (V.toList x))))

-- | 1-bit full adder
full_adder :: ANF -> ANF -> ANF -> (ANF, ANF)
full_adder a b c = (carry, ANF.xor (ANF.xor a b) c)
  where carry = ANF.xor (ANF.conj a b) (ANF.conj (ANF.xor a b) c)

-- | Big-endian ripple-carry adder
ripple_carry_adder :: [ANF] -> [ANF] -> ANF -> (ANF, [ANF])
ripple_carry_adder [] _ c = (c, [])
ripple_carry_adder _ [] c = (c, [])
ripple_carry_adder (x : xs) (y : ys) c = (c'', z : zs)
  where (c', zs) = ripple_carry_adder xs ys c
        (c'', z) = full_adder x y c'

-- | Two's complement bitvector addition
add :: ANFV -> ANFV -> ANFV
add x y =
  V.fromList (snd (ripple_carry_adder (V.toList x) (V.toList y) ANF.false))

-- | Two's complement bitvector subtraction
sub :: ANFV -> ANFV -> ANFV
sub x y =
  V.fromList (snd (ripple_carry_adder (V.toList x) (map ANF.compl (V.toList y)) ANF.true))

mul :: ANFV -> ANFV -> ANFV
mul x y = V.foldl f zero y
  where
    zero = V.replicate (V.length x) ANF.false
    f acc c = V.zipWith (ANF.mux c) (add acc2 x) acc2
      where acc2 = V.drop 1 (acc V.++ V.singleton ANF.false)

-- | Unsigned bitvector division
udiv :: ANFV -> ANFV -> ANFV
udiv x y = fst (udivrem x y)

-- | Unsigned bitvector remainder
urem :: ANFV -> ANFV -> ANFV
urem x y = snd (udivrem x y)

-- | Signed bitvector division
sdiv :: ANFV -> ANFV -> ANFV
sdiv x y = fst (sdivrem x y)

-- | Signed bitvector remainder
srem :: ANFV -> ANFV -> ANFV
srem x y = snd (sdivrem x y)

udivrem :: ANFV -> ANFV -> (ANFV, ANFV)
udivrem dividend divisor = divStep 0 ANF.false initial
  where
    n :: Int
    n = V.length dividend

    -- Given an n-bit dividend and divisor, 'initial' is the starting value of
    -- the 2n-bit "remainder register" that carries both the quotient and remainder;
    initial :: ANFV
    initial = integer n 0 V.++ dividend

    divStep :: Int -> ANF -> ANFV -> (ANFV, ANFV)
    divStep i p rr | i == n = (q `shiftL1` p, r)
      where (r, q) = V.splitAt n rr
    divStep i p rr = divStep (i+1) b (V.zipWith (ANF.mux b) (V.fromList s V.++ q) rs)
      where rs = rr `shiftL1` p
            (r, q) = V.splitAt n rs
            -- Subtract the divisor from the left half of the "remainder register"
            (b, s) = ripple_carry_adder (V.toList r) (map ANF.compl (V.toList divisor)) ANF.true

    shiftL1 :: ANFV -> ANF -> ANFV
    shiftL1 v e = V.tail v `V.snoc` e

-- Perform udivrem on the absolute value of the operands.  Then, negate the
-- quotient if the signs of the operands differ and make the sign of a nonzero
-- remainder to match that of the dividend.
sdivrem :: ANFV -> ANFV -> (ANFV, ANFV)
sdivrem dividend divisor = (q',r')
  where
    sign1 = V.head dividend
    sign2 = V.head divisor
    signXor = ANF.xor sign1 sign2
    negWhen x c = V.zipWith (ANF.mux c) (neg x) x
    dividend' = negWhen dividend sign1
    divisor' = negWhen divisor sign2
    (q, r) = udivrem dividend' divisor'
    q' = negWhen q signXor
    r' = negWhen r sign1

-- | Polynomial multiplication. Note that the algorithm works the same
-- no matter which endianness convention is used. Result length is
-- @max 0 (m+n-1)@, where @m@ and @n@ are the lengths of the inputs.
pmul :: ANFV -> ANFV -> ANFV
pmul x y = V.generate (max 0 (m + n - 1)) coeff
  where
    m = V.length x
    n = V.length y
    coeff k = foldr ANF.xor ANF.false
      [ ANF.conj (x V.! i) (y V.! j) | i <- [0 .. k], let j = k - i, i < m, j < n ]

-- | Polynomial mod with symbolic modulus. Return value has length one
-- less than the length of the modulus.
-- This implementation is optimized for the (common) case where the modulus
-- is concrete.
pmod :: ANFV -> ANFV -> ANFV
pmod x y = findmsb (V.toList y)
  where
    findmsb :: [ANF] -> ANFV
    findmsb [] = V.replicate (V.length y - 1) ANF.false -- division by zero
    findmsb (c : cs)
      | c == ANF.true = usemask cs
      | c == ANF.false = findmsb cs
      | otherwise = V.zipWith (ANF.mux c) (usemask cs) (findmsb cs)

    usemask :: [ANF] -> ANFV
    usemask m = zext (V.fromList (go (V.length x - 1) p0 z0)) (V.length y - 1)
      where
        zext v r = V.replicate (r - V.length v) ANF.false V.++ v
        msize = length m
        p0 = replicate (msize - 1) ANF.false ++ [ANF.true]
        z0 = replicate msize ANF.false

        next :: [ANF] -> [ANF]
        next [] = []
        next (b : bs) =
          let m' = map (ANF.conj b) m
              bs' = bs ++ [ANF.false]
          in zipWith ANF.xor m' bs'

        go :: Int -> [ANF] -> [ANF] -> [ANF]
        go i p acc
          | i < 0 = acc
          | otherwise =
              let px = map (ANF.conj (x V.! i)) p
                  acc' = zipWith ANF.xor px acc
                  p' = next p
              in go (i-1) p' acc'

-- | Polynomial division. Return value has length
--   equal to the first argument.
pdiv :: ANFV -> ANFV -> ANFV
pdiv x y = fst (pdivmod x y)

-- Polynomial div/mod: resulting lengths are as in Cryptol.

-- TODO: probably this function should be disentangled to only compute
-- division, given that we have a separate polynomial modulus algorithm.
pdivmod :: ANFV -> ANFV -> (ANFV, ANFV)
pdivmod x y = findmsb (V.toList y)
  where
    findmsb :: [ANF] -> (ANFV, ANFV)
    findmsb (c : cs) = muxPair c (usemask cs) (findmsb cs)
    findmsb [] = (x, V.replicate (V.length y - 1) ANF.false) -- division by zero

    usemask :: [ANF] -> (ANFV, ANFV)
    usemask mask = (q, r)
      where
        (qs, rs) = pdivmod_helper (V.toList x) mask
        z = ANF.false
        qs' = map (const z) rs ++ qs
        rs' = replicate (V.length y - 1 - length rs) z ++ rs
        q = V.fromList qs'
        r = V.fromList rs'

    muxPair :: ANF -> (ANFV, ANFV) -> (ANFV, ANFV) -> (ANFV, ANFV)
    muxPair c a b
      | c == ANF.true = a
      | c == ANF.false = b
      | otherwise = (V.zipWith (ANF.mux c) (fst a) (fst b), V.zipWith (ANF.mux c) (snd a) (snd b))

-- Divide ds by (1 : mask), giving quotient and remainder. All
-- arguments and results are big-endian. Remainder has the same length
-- as mask (but limited by length ds); total length of quotient ++
-- remainder = length ds.
pdivmod_helper :: [ANF] -> [ANF] -> ([ANF], [ANF])
pdivmod_helper ds mask = go (length ds - length mask) ds
  where
    go :: Int -> [ANF] -> ([ANF], [ANF])
    go n cs | n <= 0 = ([], cs)
    go _ []          = error "Data.AIG.Operations.pdiv: impossible"
    go n (c : cs)    = (c : qs, rs)
      where cs' = mux_add c cs mask
            (qs, rs) = go (n - 1) cs'

    mux_add :: ANF -> [ANF] -> [ANF] -> [ANF]
    mux_add c (x : xs) (y : ys) = ANF.mux c (ANF.xor x y) x : mux_add c xs ys
    mux_add _ []       (_ : _ ) = error "pdiv: impossible"
    mux_add _ xs       []       = xs
