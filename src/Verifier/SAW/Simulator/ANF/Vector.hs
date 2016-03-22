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

eq :: ANFV -> ANFV -> ANF
eq x y = V.foldr ANF.conj ANF.true (V.zipWith ANF.iff x y)

ule :: ANFV -> ANFV -> ANF
ule = error "unimplemented: ule"

ult :: ANFV -> ANFV -> ANF
ult = error "unimplemented: ult"

sle :: ANFV -> ANFV -> ANF
sle = error "unimplemented: sle"

slt :: ANFV -> ANFV -> ANF
slt = error "unimplemented: slt"

neg :: ANFV -> ANFV
neg = error "unimplemented: neg"

add :: ANFV -> ANFV -> ANFV
add = error "unimplemented: add"

sub :: ANFV -> ANFV -> ANFV
sub = error "unimplemented: sub"

mul :: ANFV -> ANFV -> ANFV
mul = error "unimplemented: mul"

udiv :: ANFV -> ANFV -> ANFV
udiv = error "unimplemented: udiv"

urem :: ANFV -> ANFV -> ANFV
urem = error "unimplemented: urem"

sdiv :: ANFV -> ANFV -> ANFV
sdiv = error "unimplemented: sdiv"

srem :: ANFV -> ANFV -> ANFV
srem = error "unimplemented: srem"

-- | Polynomial multiplication. Note that the algorithm works the same
--   no matter which endianness convention is used.  Result length is
--   @max 0 (m+n-1)@, where @m@ and @n@ are the lengths of the inputs.
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
    usemask m = zext (V.fromList (go (V.length x - 1) p0 z0)) (length y - 1)
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
