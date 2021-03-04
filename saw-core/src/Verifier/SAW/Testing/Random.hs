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
  ( FirstOrderType(..), FirstOrderValue(..)
  , scFirstOrderValue, asFirstOrderTypeMaybe
  )

import Verifier.SAW.Recognizer (asBoolType, asPi, asEq)
import Verifier.SAW.SharedTerm
  ( scApplyAll, scGetModuleMap, scWhnf, SharedContext, Term
  , looseVars
  )
import Verifier.SAW.Simulator.Concrete (evalSharedTerm, CValue)
import Verifier.SAW.Simulator.Value (Value(..), TValue(..))
import Verifier.SAW.Term.Functor (emptyBitSet)
--import Verifier.SAW.TypedAST (FieldName)
import Verifier.SAW.Utils (panic)


#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>), Applicative)
import Data.Traversable (traverse)
#endif
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Random
import Data.Functor.Compose (Compose(..))
import qualified Data.Map as Map
import Data.Text (Text)
import System.Random.TF (newTFGen, TFGen)

----------------------------------------------------------------
-- Interface.

-- | Run @scRunTests@ in 'IO' using 'System.Random.TF.TFGen' for generation.
--
-- The caller should use @scTestableType@ to (maybe) compute the 'gens'.
scRunTestsTFIO ::
  SharedContext -> Integer -> Term -> [RandT TFGen IO FirstOrderValue] ->
  IO (Maybe [FirstOrderValue])
scRunTestsTFIO sc numTests fun gens = do
  g <- newTFGen
  evalRandT (scRunTests sc numTests fun gens) g

-- | Call @scRunTest@ many times, returning the first failure if any.
scRunTests :: (Functor m, MonadIO m, MonadRandom m) => SharedContext ->
  Integer -> Term -> [m FirstOrderValue] -> m (Maybe [FirstOrderValue])
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
  Term -> [m FirstOrderValue] -> m (Maybe [FirstOrderValue])
scRunTest sc fun gens = do
  xs <- sequence gens
  result <- liftIO $ apply xs
  case result of
    VBool True -> return Nothing
    VBool False -> do
      return $ Just xs
    TValue (VDataType "Prelude.Eq" [TValue VBoolType, VBool x, VBool y]) -> do
      return $ if x == y then Nothing else Just xs
    _ -> panic "Type error while running test"
         [ "Expected a boolean, but got:"
         , show result ]
  where
    apply :: [FirstOrderValue] -> IO CValue
    apply xs = do
      xs' <- mapM (scFirstOrderValue sc) xs
      app <- scApplyAll sc fun xs'
      modmap <- scGetModuleMap sc
      return $ evalSharedTerm modmap Map.empty app

-- | Given a function type, compute generators for the function's
-- arguments. The supported function types are of the form
--
--   'FirstOrderType -> ... -> FirstOrderType -> Bool'
--   or
--   'FirstOrderType -> ... -> FirstOrderType -> Eq (...) (...)'
--      for equalities on boolean values.
--
-- 'Nothing' is returned when attempting to generate arguments for
-- functions of unsupported type.
scTestableType :: (Applicative m, Functor m, MonadRandom m) =>
  SharedContext -> Term -> MaybeT IO [(Text, m FirstOrderValue)]
scTestableType sc ty =
  do ty' <- lift (scWhnf sc ty)
     case ty' of
       (asPi -> Just (nm, dom, rng)) | looseVars rng == emptyBitSet ->
         do fot <- asFirstOrderTypeMaybe sc dom
            case getCompose (randomFirstOrderValue fot) of
              Nothing -> mzero
              Just domGen ->
                do rngGens <- scTestableType sc rng
                   return ((nm,domGen) : rngGens)

       (asBoolType -> Just ()) -> return []
       (asEq -> Just (asBoolType -> Just (),_,_)) -> return []
       _ -> mzero

----------------------------------------------------------------


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

