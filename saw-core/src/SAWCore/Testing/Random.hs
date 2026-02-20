{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Module      :  SAWCore.Testing.Random
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  saw@galois.com
-- Stability   :  experimental
-- Portability :  portable
--
-- This module generates random values for 'FiniteValue.FiniteType' types.
--
-- Based on 'Cryptol.Testing.Random'.

module SAWCore.Testing.Random where

import SAWCore.FiniteValue
  ( FirstOrderFloat(..), FirstOrderType(..), FirstOrderValue(..)
  , scFirstOrderValue
  )

import SAWCore.FloatHelpers (fpCheckStatus, fpOpts)
import SAWCore.Module (ModuleMap)
import SAWCore.Name (VarName(..))
import SAWCore.SATQuery
import SAWCore.SharedTerm
  ( scGetModuleMap, SharedContext, Term
  , scInstantiate
  )
import SAWCore.Simulator.Concrete (evalSharedTerm) -- , CValue)
import SAWCore.Simulator.Value (Value(..)) -- , TValue(..))

import qualified Control.Monad.Fail as F
import Control.Monad.Random
import Data.Bits (Bits(..))
import Data.Functor.Compose (Compose(..))
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Ratio (numerator, denominator)
import qualified Data.Set as Set
import LibBF
import Numeric.Natural (Natural)
import System.Random.TF (newTFGen, TFGen)



randomFirstOrderValue :: (Applicative m, Functor m, MonadRandom m) =>
  FirstOrderType -> Compose Maybe m FirstOrderValue
randomFirstOrderValue FOTBit =
  Compose (Just (FOVBit <$> getRandom))
randomFirstOrderValue FOTInt =
  Compose (Just (FOVInt <$> randomInt))
randomFirstOrderValue (FOTIntMod m) =
  Compose (Just (FOVIntMod m <$> getRandomR (0, toInteger m - 1)))
randomFirstOrderValue (FOTFloat e p) =
  Compose (Just ((FOVFloat . FirstOrderFloat e p) <$> randomBigFloat e p))
randomFirstOrderValue (FOTVec n FOTBit) =
  Compose (Just (FOVWord n <$> getRandomR (0, 2^n - 1)))
randomFirstOrderValue (FOTVec n t) =
  FOVVec t <$> replicateM (fromIntegral n) (randomFirstOrderValue t)
randomFirstOrderValue (FOTTuple ts) =
  FOVTuple <$> traverse randomFirstOrderValue ts
randomFirstOrderValue (FOTRec fs) =
  FOVRec <$> traverse randomFirstOrderValue fs
randomFirstOrderValue (FOTArray _ _) = Compose Nothing


-- TODO this is really a hack
randomInt :: MonadRandom m => m Integer
randomInt = getRandomR (-10^(6::Int), 10^(6::Int))

randomBigFloat ::
  forall m.
  MonadRandom m =>
  -- | Exponent width
  Natural ->
  -- | Precision width
  Natural ->
  m BigFloat
randomBigFloat e p = do
  let sz :: Integer
      sz = 5
  x <- getRandomR (0, 10*(sz+1))
  if | x < 2    -> pure bfNaN
     | x < 4    -> pure bfPosInf
     | x < 6    -> pure bfNegInf
     | x < 8    -> pure bfPosZero
     | x < 10   -> pure bfNegZero
     | x <= sz       -> randomSubnormal  -- about 10% of the time
     | x <= 4*(sz+1) -> randomBinary     -- about 40%
     | otherwise     -> randomNormal (toInteger sz)  -- remaining ~50%
  where
    opts = fpOpts e p NearEven

    eInt = fromIntegral @Natural @Int e
    pInt = fromIntegral @Natural @Int p

    emax = bit eInt - 1
    smax = bit pInt - 1

    -- Generates floats uniformly chosen from among all bitpatterns.
    randomBinary :: m BigFloat
    randomBinary = do
      v <- getRandomR (0, bit (eInt+pInt) - 1)
      pure $ bfFromBits opts v

    -- Generates floats corresponding to subnormal values. These are values
    -- with 0 biased exponent and nonzero mantissa.
    randomSubnormal :: m BigFloat
    randomSubnormal = do
      sgn <- getRandom
      v <- getRandomR (1, bit pInt - 1)
      let bf = bfFromBits opts v
      let bf' = if sgn then bfNeg bf else bf
      pure bf'

    -- Generates floats where the exponent and mantissa are scaled by the size.
    randomNormal :: Integer -> m BigFloat
    randomNormal sz = do
      sgn <- getRandom
      ex <- getRandomR ((1-emax)*sz `div` 100, (sz*emax) `div` 100)
      mag <- getRandomR (1, max 1 ((sz*smax) `div` 100))
      let r  = fromInteger mag ^^ (ex - widthInteger mag)
      let r' = if sgn then negate r else r
      let bf = fpCheckStatus $
               bfDiv
                 opts
                 (bfFromInteger (numerator r'))
                 (bfFromInteger (denominator r'))
      pure bf

    -- Compute the number of bits required to represent the given integer.
    widthInteger :: Integer -> Integer
    widthInteger x = go' 0 (if x < 0 then complement x else x)
      where
        go s 0 = s
        go s n = let s' = s + 1 in s' `seq` go s' (n `shiftR` 1)

        go' s n
          | n < bit 32 = go s n
          | otherwise  = let s' = s + 32 in s' `seq` go' s' (n `shiftR` 32)

execTest ::
  (F.MonadFail m, MonadRandom m, MonadIO m) =>
  SharedContext ->
  ModuleMap ->
  Map VarName (m FirstOrderValue) ->
  Term ->
  m (Maybe [(VarName, FirstOrderValue)])
execTest sc mmap vars tm =
  do testVec <- sequence vars
     tm' <- liftIO $
             do argMap0 <- traverse (scFirstOrderValue sc) testVec
                let argMap = IntMap.fromList [ (vnIndex x, v) | (x, v) <- Map.toList argMap0 ]
                scInstantiate sc argMap tm
     case evalSharedTerm mmap Map.empty Map.empty tm' of
       -- satisfaible, return counterexample
       VBool True  -> return (Just (Map.toList testVec))
       -- not satisfied by this test vector
       VBool False -> return Nothing
       _ -> fail "execTest: expected boolean result from random testing"

prepareSATQuery ::
  (MonadRandom m, F.MonadFail m, MonadIO m) =>
  SharedContext ->
  SATQuery ->
  IO (m (Maybe [(VarName, FirstOrderValue)]))
prepareSATQuery sc satq
  | Set.null (satUninterp satq) =
       do varmap <- traverse prepareVar (satVariables satq)
          t <- satQueryAsTerm sc satq
          mmap <- scGetModuleMap sc
          return (execTest sc mmap varmap t)
  | otherwise = fail "Random testing cannot handle uninterpreted functions"

 where
   prepareVar fot =
     case randomFirstOrderValue fot of
       Compose (Just v) -> pure v
       _ -> fail ("Cannot randomly test argument of type: " ++ show fot)

runManyTests ::
  RandT TFGen IO (Maybe [(VarName, FirstOrderValue)]) ->
  Integer ->
  IO (Maybe [(VarName, FirstOrderValue)])
runManyTests m numtests = evalRandT (loop numtests) =<< newTFGen
  where
    loop n
      | n > 0 =
          m >>= \case
            Nothing  -> loop (n-1)
            Just cex -> return (Just cex)

      | otherwise = return Nothing
