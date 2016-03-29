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

-- | Signed less-than-or-equal
sle :: ANFV -> ANFV -> ANF
sle = error "unimplemented: sle"

-- | Signed less-than
slt :: ANFV -> ANFV -> ANF
slt = error "unimplemented: slt"

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
mul x y = go (fmap (const ANF.false) x) (V.toList y)
  where
    go acc [] = acc
    go acc (c : cs) = go (V.zipWith (ANF.mux c) (add acc2 x) acc2) cs
      where acc2 = V.drop 1 (acc V.++ V.singleton ANF.false)

udiv :: ANFV -> ANFV -> ANFV
udiv = error "unimplemented: udiv"

urem :: ANFV -> ANFV -> ANFV
urem = error "unimplemented: urem"

sdiv :: ANFV -> ANFV -> ANFV
sdiv = error "unimplemented: sdiv"

srem :: ANFV -> ANFV -> ANFV
srem = error "unimplemented: srem"

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

pdiv :: ANFV -> ANFV -> ANFV
pdiv = error "unimplemented: pdiv"

integer :: Int -> Integer -> ANFV
integer width x = V.reverse (V.generate width (ANF.constant . testBit x))
