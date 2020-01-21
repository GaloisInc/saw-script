{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Module      :  Verifier.SAW.Testing.Random
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  jhendrix@galois.com, conathan@galois.com
-- Stability   :  experimental
-- Portability :  portable
--
-- This module generates random values for 'FiniteValue.FiniteType' types.
--
-- Based on 'Cryptol.Testing.Random'.

module Verifier.SAW.Testing.Random where

import Verifier.SAW.FiniteValue
  (asFiniteTypePure, scFiniteValue, FiniteType(..), FiniteValue(..))
import Verifier.SAW.Recognizer (asBoolType, asPi, asEq)
import Verifier.SAW.SharedTerm
  (scApplyAll, scGetModuleMap, scWhnf, SharedContext, Term)
import Verifier.SAW.Simulator.Concrete (evalSharedTerm, CValue)
import Verifier.SAW.Simulator.Value (Value(..))
import Verifier.SAW.TypedAST (FieldName)
import Verifier.SAW.Utils (panic)

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>), Applicative)
import Data.Traversable (traverse)
#endif
import Control.Monad.Random
import Data.Map (Map)
import qualified Data.Map as Map
import Numeric.Natural (Natural)
import System.Random.TF (newTFGen, TFGen)

----------------------------------------------------------------
-- Interface.

-- | Run @scRunTests@ in 'IO' using 'System.Random.TF.TFGen' for generation.
--
-- The caller should use @scTestableType@ to (maybe) compute the 'gens'.
scRunTestsTFIO ::
  SharedContext -> Integer -> Term -> [RandT TFGen IO FiniteValue] ->
  IO (Maybe [FiniteValue])
scRunTestsTFIO sc numTests fun gens = do
  g <- newTFGen
  evalRandT (scRunTests sc numTests fun gens) g

-- | Call @scRunTest@ many times, returning the first failure if any.
scRunTests :: (Functor m, MonadIO m, MonadRandom m) => SharedContext ->
  Integer -> Term -> [m FiniteValue] -> m (Maybe [FiniteValue])
scRunTests sc numTests fun gens =
  if numTests < 0 then
    panic "scRunTests:" ["number of tests must be non-negative"]
  else do
    let oneTest = scRunTest sc fun gens
    -- Use 'msum' to collapse the embedded 'Maybe's, retaining the
    -- first counter example, if any.
    msum <$> replicateM (fromIntegral numTests) oneTest

{- | Apply a testable value to some randomly-generated arguments.
     Returns `Nothing` if the function returned `True`, or
     `Just counterexample` if it returned `False`.

    Use @scTestableType@ to compute the input generators.

    Please note that this function assumes that the generators match
    the supplied value, otherwise we'll panic.
 -}
scRunTest :: (MonadIO m, MonadRandom m) => SharedContext ->
  Term -> [m FiniteValue] -> m (Maybe [FiniteValue])
scRunTest sc fun gens = do
  xs <- sequence gens
  result <- liftIO $ apply xs
  case result of
    VBool True -> return $ Nothing
    VBool False -> do
      return $ Just xs
    VDataType "Prelude.Eq" [VBoolType, VBool x, VBool y] -> do
      return $ if x == y then Nothing else Just xs
    _ -> panic "Type error while running test"
         [ "Expected a boolean, but got:"
         , show result ]
  where
    apply :: [FiniteValue] -> IO CValue
    apply xs = do
      xs' <- mapM (scFiniteValue sc) xs
      app <- scApplyAll sc fun xs'
      modmap <- scGetModuleMap sc
      return $ evalSharedTerm modmap Map.empty app

-- | Given a function type, compute generators for the function's
-- arguments. The supported function types are of the form
--
--   'FiniteType -> ... -> FiniteType -> Bool'
--   or
--   'FiniteType -> ... -> FiniteType -> Eq (...) (...)'
--
-- and 'Nothing' is returned when attempting to generate arguments for
-- functions of unsupported type.
scTestableType :: (Applicative m, Functor m, MonadRandom m) =>
  SharedContext -> Term -> IO (Maybe [m FiniteValue])
scTestableType sc ty = do
  ty' <- scWhnf sc ty
  case ty' of
    (asPi -> Just (_nm, asFiniteTypePure -> Just dom, rng)) -> do
      let domGen = randomFiniteValue dom
      rngGens <- scTestableType sc rng
      return $ (domGen :) <$> rngGens
    (asBoolType -> Just ()) -> return $ Just []
    (asEq -> Just _) -> return $ Just []
    _ -> return Nothing

----------------------------------------------------------------

randomFiniteValue :: (Applicative m, Functor m, MonadRandom m) =>
  FiniteType -> m FiniteValue
randomFiniteValue FTBit = randomBit
randomFiniteValue (FTVec n FTBit) = randomWord n
randomFiniteValue (FTVec n t) = randomVec n t
randomFiniteValue (FTTuple ts) = randomTuple ts
randomFiniteValue (FTRec fields) = randomRec fields

----------------------------------------------------------------
-- The value generators below follow a pattern made clear in the
-- definition of 'randomFiniteValue' above: each 'FiniteValue' value
-- generator takes the same (non-constant) arguments as the
-- corresponding 'FiniteType' type constructor.

-- | Generate a random bit value.
randomBit :: (Functor m, MonadRandom m) => m FiniteValue
randomBit = FVBit <$> getRandom

-- | Generate a random word of the given length (i.e., a value of type @[w]@)
randomWord :: (Functor m, MonadRandom m) => Natural -> m FiniteValue
randomWord w = FVWord w <$> getRandomR (0, 2^w - 1)

{- | Generate a random vector.  Generally, this should be used for sequences
other than bits.  For sequences of bits use "randomWord".  The difference
is mostly about how the results will be displayed. -}
randomVec :: (Applicative m, Functor m, MonadRandom m) =>
  Natural -> FiniteType -> m FiniteValue
randomVec w t =
  FVVec t <$> replicateM (fromIntegral w) (randomFiniteValue t)

-- | Generate a random tuple value.
randomTuple :: (Applicative m, Functor m, MonadRandom m) =>
  [FiniteType] -> m FiniteValue
randomTuple ts = FVTuple <$> mapM randomFiniteValue ts

-- | Generate a random record value.
randomRec :: (Applicative m, Functor m, MonadRandom m) =>
  Map FieldName FiniteType -> m FiniteValue
randomRec fieldTys = FVRec <$> traverse randomFiniteValue fieldTys

_test :: IO ()
_test = do
  s <- evalRandIO $ randomFiniteValue (FTVec 16 (FTVec 1 FTBit))
  print s
