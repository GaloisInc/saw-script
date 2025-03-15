{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Module      :  SAWCore.Testing.Random
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  jhendrix@galois.com, conathan@galois.com
-- Stability   :  experimental
-- Portability :  portable
--
-- This module generates random values for 'FiniteValue.FiniteType' types.
--
-- Based on 'Cryptol.Testing.Random'.

module SAWCore.Testing.Random where

import SAWCore.FiniteValue
  ( FirstOrderType(..), FirstOrderValue(..), scFirstOrderValue )

import SAWCore.Module (ModuleMap)
import SAWCore.SATQuery
import SAWCore.SharedTerm
  ( scGetModuleMap, SharedContext, Term
  , ExtCns(..), scInstantiateExt
  )
import SAWCore.Simulator.Concrete (evalSharedTerm) -- , CValue)
import SAWCore.Simulator.Value (Value(..)) -- , TValue(..))


#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>), Applicative)
import Data.Traversable (traverse)
#endif
import qualified Control.Monad.Fail as F
import Control.Monad.Random
import Data.Functor.Compose (Compose(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Random.TF (newTFGen, TFGen)



randomFirstOrderValue :: (Applicative m, Functor m, MonadRandom m) =>
  FirstOrderType -> Compose Maybe m FirstOrderValue
randomFirstOrderValue FOTBit =
  Compose (Just (FOVBit <$> getRandom))
randomFirstOrderValue FOTInt =
  Compose (Just (FOVInt <$> randomInt))
randomFirstOrderValue (FOTIntMod m) =
  Compose (Just (FOVIntMod m <$> getRandomR (0, toInteger m - 1)))
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



execTest ::
  (F.MonadFail m, MonadRandom m, MonadIO m) =>
  SharedContext ->
  ModuleMap ->
  Map.Map (ExtCns Term) (m FirstOrderValue) ->
  Term ->
  m (Maybe [(ExtCns Term, FirstOrderValue)])
execTest sc mmap vars tm =
  do testVec <- sequence vars
     tm' <- liftIO $
             do argMap0 <- traverse (scFirstOrderValue sc) testVec
                let argMap = Map.fromList [ (ecVarIndex ec, v) | (ec,v) <- Map.toList argMap0 ]
                scInstantiateExt sc argMap tm
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
  IO (m (Maybe [(ExtCns Term, FirstOrderValue)]))
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
  RandT TFGen IO (Maybe [(ExtCns Term, FirstOrderValue)]) ->
  Integer ->
  IO (Maybe [(ExtCns Term, FirstOrderValue)])
runManyTests m numtests = evalRandT (loop numtests) =<< newTFGen
  where
    loop n
      | n > 0 =
          m >>= \case
            Nothing  -> loop (n-1)
            Just cex -> return (Just cex)

      | otherwise = return Nothing
