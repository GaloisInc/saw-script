{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{- |
Module      : SAWCore.FloatHelpers
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Utility functions for dealing with "LibBF". This is heavily inspired by
Cryptol's @Cryptol.Backend.FloatHelpers@ module.
-}
module SAWCore.FloatHelpers
  ( fpCheckStatus
  , fpOpts
  , fpRound
  , floatFromInteger
  , floatFromRational
  , floatToRational
  , floatToInteger
  , NotRationalError(..)
  , ppNotRationalError
  , floatFromBits
  , floatToBits
  , floatToBV
  , floatToSBV
  , NotBitvectorError(..)
  , ppNotBitvectorError
  ) where

import Data.Bits (Bits(..))
import Data.Ratio (numerator, denominator)
import qualified Data.Text as Text
import LibBF
import Numeric.Natural (Natural)

import SAWCore.Panic (panic)

-- | Check that we didn't get an unexpected status.
fpCheckStatus :: (BigFloat, Status) -> BigFloat
fpCheckStatus (r,s) =
  case s of
    MemError  -> panic "fpCheckStatus" [ "libBF: Memory error" ]
    _         -> r

-- | Make LibBF options for the given precision and rounding mode.
fpOpts :: Natural -> Natural -> RoundMode -> BFOpts
fpOpts e p r =
  case ok of
    Just opts -> opts
    Nothing   -> panic "fpOpts" [ "Invalid Float size"
                                , "exponent: " <> Text.pack (show e)
                                , "precision: " <> Text.pack (show p)
                                ]
  where
    ok :: Maybe BFOpts
    ok = do eb <- rng expBits expBitsMin expBitsMax e
            pb <- rng precBits precBitsMin precBitsMax p
            pure (eb <> pb <> allowSubnormal <> rnd r)

    rng ::
      forall a.
      Integral a =>
      (a -> BFOpts) ->
      Int ->
      Int ->
      Natural ->
      Maybe BFOpts
    rng f a b x =
      if fromIntegral @Int @Natural a <= x && x <= fromIntegral @Int @Natural b
        then Just (f (fromIntegral @Natural @a x))
        else Nothing

-- | Mapping from the rounding modes defined in the @Float.cry@ module to the
-- rounding modes of LibBF.
fpRound :: Integer -> Maybe RoundMode
fpRound n =
  case n of
    0 -> Just NearEven
    1 -> Just NearAway
    2 -> Just ToPosInf
    3 -> Just ToNegInf
    4 -> Just ToZero
    _ -> Nothing

-- | Make a floating point number from an integer, using the given rounding
-- mode.
floatFromInteger :: BFOpts -> Integer -> BigFloat
floatFromInteger opts i = fpCheckStatus (bfRoundFloat opts (bfFromInteger i))

-- | Make a floating point number from a rational, using the given rounding
-- mode.
floatFromRational :: Natural -> Natural -> RoundMode -> Rational -> BigFloat
floatFromRational e p r rat =
  fpCheckStatus $
  if den == 1
    then bfRoundFloat opts num
    else bfDiv opts num (bfFromInteger den)
  where
    opts  = fpOpts e p r

    num   = bfFromInteger (numerator rat)
    den   = denominator rat

-- | Convert a floating-point number to a 'Rational' if possible. Return 'Left'
-- if the input is infinite or NaN.
floatToRational :: BigFloat -> Either NotRationalError Rational
floatToRational bf =
  case bfToRep bf of
    BFNaN -> Left IsNaN
    BFRep s num ->
      case num of
        Inf  -> Left IsInf
        Zero -> Right 0
        Num i ev -> Right $
          case s of
            Pos -> ab
            Neg -> negate ab
          where ab = fromInteger i * (2 ^^ ev)

-- | Convert a floating point number to an integer, if possible. Return 'Left'
-- if the input is infinite or NaN.
floatToInteger :: RoundMode -> BigFloat -> Either NotRationalError Integer
floatToInteger r fp =
  do rat <- floatToRational fp
     pure $
       case r of
         NearEven -> round rat
         NearAway -> roundAway rat
         ToPosInf -> ceiling rat
         ToNegInf -> floor rat
         ToZero   -> truncate rat
         _        -> panic "floatToInteger"
                           ["Unexpected rounding mode", Text.pack (show r)]
  where
    -- | Evaluate a rational to an integer with rounding away from zero.
    roundAway :: Rational -> Integer
    roundAway r' = truncate (r' + signum r' * 0.5)

-- | Why a floating-point value cannot be represented as a 'Rational'.
data NotRationalError = IsNaN | IsInf

ppNotRationalError :: NotRationalError -> String
ppNotRationalError IsNaN = "NaN value cannot be represented as a Rational"
ppNotRationalError IsInf = "Infinite value cannot be represented as a Rational"

floatFromBits ::
  Natural {- ^ Exponent width -} ->
  Natural {- ^ Precision width -} ->
  Integer {- ^ Raw bits -} ->
  BigFloat
floatFromBits e p bv = bfFromBits (fpOpts e p NearEven) bv

-- | Turn a float into raw bits.
-- @NaN@ is represented as a positive "quiet" @NaN@
-- (most significant bit in the significand is set, the rest of it is 0)
floatToBits :: Natural -> Natural -> BigFloat -> Integer
floatToBits e p bf = bfToBits (fpOpts e p NearEven) bf

-- | Convert a floating point number to an unsigned bitvector. If the value of
-- the float does not lie within the range of possible unsigned bitvector
-- values, then this will return 'Left'.
floatToBV :: Natural -> RoundMode -> BigFloat -> Either NotBitvectorError Integer
floatToBV w r bf =
  case floatToInteger r bf of
    Left e -> Left $ IsSpecialValue e
    Right i ->
      if 0 <= i && i <= maxUnsigned
        then Right i
        else Left IsOutsideRange
  where
    maxUnsigned :: Integer
    maxUnsigned = bit (fromIntegral @Natural @Int w) - 1

-- | Convert a floating point number to a signed bitvector. If the value of the
-- float does not lie within the range of possible signed bitvector values,
-- then this will return 'Left'.
floatToSBV :: Natural -> RoundMode -> BigFloat -> Either NotBitvectorError Integer
floatToSBV w r bf =
  case floatToInteger r bf of
    Left e -> Left $ IsSpecialValue e
    Right i ->
      if minSigned <= i && i <= maxSigned
        then Right i
        else Left IsOutsideRange
  where
    signedUpperBound :: Integer
    signedUpperBound = bit (fromIntegral @Natural @Int w - 1)

    minSigned, maxSigned :: Integer
    minSigned = negate signedUpperBound
    maxSigned = signedUpperBound - 1

-- | Why a floating-point value cannot be represented as a bitvector.
data NotBitvectorError
  = IsSpecialValue NotRationalError
    -- ^ The value is infinite or NaN.
  | IsOutsideRange
    -- ^ The value lies outside the range of possible bitvector values.

ppNotBitvectorError :: NotBitvectorError -> String
ppNotBitvectorError (IsSpecialValue e) = ppNotRationalError e
ppNotBitvectorError IsOutsideRange = "Float lies outside range of possible bitvector values"
