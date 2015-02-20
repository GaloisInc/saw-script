{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Verifier.SAW.Simulator.SBV.SWord where

import Data.Bits
import Control.Monad (replicateM)
import System.Random

import Data.SBV
import Data.SBV.Internals

import Verifier.SAW.Utils (panic)

-- Phantom BV type -------------------------------------------------------------

-- | This datatype is used only as a phantom type argument for the SBV
-- type. We declare it as a void type, along with a collection of
-- dummy class instances to make the SBV type work.
data BV

instance Eq BV where
  (==)         = error "BV"
  (/=)         = error "BV"

instance Ord BV where
  compare      = error "BV"

instance Num BV where
  (+)          = error "BV"
  (*)          = error "BV"
  abs          = error "BV"
  signum       = error "BV"
  negate       = error "BV"
  fromInteger  = error "BV"

instance Bits BV where
  (.&.)        = error "BV"
  (.|.)        = error "BV"
  xor          = error "BV"
  complement   = error "BV"
  shift        = error "BV"
  rotate       = error "BV"
  bitSize      = error "BV"
  bitSizeMaybe = error "BV"
  isSigned     = error "BV"
  testBit      = error "BV"
  bit          = error "BV"
  popCount     = error "BV"

instance HasKind BV where
  kindOf       = error "BV"

instance SymWord BV where
  literal      = error "BV"
  fromCW       = error "BV"
  mkSymWord    = error "BV"

instance SDivisible BV where
  sQuotRem     = error "BV"
  sDivMod      = error "BV"

instance SIntegral BV

-- SWord type ------------------------------------------------------------------

type SWord = SBV BV

instance FromBits SWord where
  fromBitsLE bs = go (literalSWord (length bs) 0) 0 bs
    where go !acc _  []     = acc
          go !acc !i (x:xs) = go (ite x (setBit acc i) acc) (i+1) xs

instance SDivisible SWord where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SignCast SWord SWord where

  signCast (SBV (KBounded _ w) (Left (cwVal -> CWInteger x))) = genLiteral k x
    where k = KBounded True w
  signCast x@(SBV (KBounded _ w) _) = SBV k (Right (cache y))
    where
      k = KBounded True w
      y st = do xsw <- sbvToSW st x
                newExpr st k (SBVApp (Extract (w - 1) 0) [xsw])
  signCast _ = panic "Verifier.SAW.Simulator.SBV.SWord"
                 [ "signCast called on non-bitvector value" ]

  unsignCast (SBV (KBounded _ w) (Left (cwVal -> CWInteger x))) = genLiteral k x
    where k = KBounded False w
  unsignCast x@(SBV (KBounded _ w) _) = SBV k (Right (cache y))
    where
      k = KBounded False w
      y st = do xsw <- sbvToSW st x
                newExpr st k (SBVApp (Extract (w - 1) 0) [xsw])
  unsignCast _ = panic "Verifier.SAW.Simulator.SBV.SWord"
                   [ "unsignCast called on non-bitvector value" ]


literalSWord :: Int -> Integer -> SWord
literalSWord w i = genLiteral (KBounded False w) i

extract :: Int -> Int -> SWord -> SWord
extract i j x@(SBV (KBounded s _) _) =
  case x of
    _ | i < j -> SBV k (Left (CW k (CWInteger 0)))
    SBV _ (Left cw) ->
      case cw of
        CW _ (CWInteger v) -> SBV k (Left (normCW (CW k (CWInteger (v `shiftR` j)))))
        _ -> panic "Verifier.SAW.Simulator.SBV.SWord.extract" [ "non-integer concrete word" ]
    _ -> SBV k (Right (cache y))
      where y st = do sw <- sbvToSW st x
                      newExpr st k (SBVApp (Extract i j) [sw])
  where
    k = KBounded s (i - j + 1)
extract _ _ _ = panic "Verifier.SAW.Simulator.SBV.SWord.extract" [ "non-bitvector value" ]

cat :: SWord -> SWord -> SWord
cat x y | intSizeOf x == 0 = y
        | intSizeOf y == 0 = x
cat x@(SBV _ (Left a)) y@(SBV _ (Left b)) =
  case (a, b) of
    (CW _ (CWInteger m), CW _ (CWInteger n)) ->
      SBV k (Left (CW k (CWInteger ((m `shiftL` (intSizeOf y) .|. n)))))
    _ -> panic "Verifier.SAW.Simulator.SBV.SWord.cat" [ "non-integer concrete word" ]
  where k = KBounded False (intSizeOf x + intSizeOf y)
cat x y = SBV k (Right (cache z))
  where k = KBounded False (intSizeOf x + intSizeOf y)
        z st = do xsw <- sbvToSW st x
                  ysw <- sbvToSW st y
                  newExpr st k (SBVApp Join [xsw, ysw])

randomSWord :: Int -> IO SWord
randomSWord w = do
  bs <- replicateM w randomIO
  let x = sum [ bit i | (i, b) <- zip [0..] bs, b ]
  return (genLiteral (KBounded False w) (x :: Integer))

mkSymSWord :: Maybe Quantifier -> Maybe String -> Int -> Symbolic SWord
mkSymSWord mbQ mbNm w =
  mkSymSBVWithRandom (randomSWord w) mbQ (KBounded False w) mbNm

forallSWord :: String -> Int -> Symbolic SWord
forallSWord nm w = mkSymSWord (Just ALL) (Just nm) w

forallSWord_ :: Int -> Symbolic SWord
forallSWord_ w = mkSymSWord (Just ALL) Nothing w

existsSWord :: String -> Int -> Symbolic SWord
existsSWord nm w = mkSymSWord (Just EX) (Just nm) w

existsSWord_ :: Int -> Symbolic SWord
existsSWord_ w = mkSymSWord (Just EX) Nothing w
