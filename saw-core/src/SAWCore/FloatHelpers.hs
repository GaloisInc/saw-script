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
  , floatToRational
  , NotRationalError(..)
  ) where

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

-- | Convert a floating-point number to a 'Rational' if possible.
floatToRational :: BigFloat -> Either NotRationalError Rational
floatToRational bf =
  case bfToRep bf of
    BFNaN -> Left IsNaN
    BFRep s num ->
      case num of
        Inf  -> Left $ IsInf s
        Zero -> Right 0
        Num i ev -> Right $
          case s of
            Pos -> ab
            Neg -> negate ab
          where ab = fromInteger i * (2 ^^ ev)

-- | Why a floating-point value cannot be represented as a 'Rational'.
data NotRationalError = IsNaN | IsInf Sign
