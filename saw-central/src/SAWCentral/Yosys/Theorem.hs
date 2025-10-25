{- |
Module      : SAWCentral.Yosys.Theorem
Description : Utilities for rewriting/compositional verification of HDL modules
License     : BSD3
Maintainer  : sbreese
Stability   : experimental
-}

{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module SAWCentral.Yosys.Theorem where
 
import Control.Lens.TH (makeLenses)

import Control.Lens ((^.))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)
import Control.Monad.Catch (MonadThrow)

import Data.Text (Text)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Text.URI as URI

import qualified SAWCore.Cache as SC
import qualified SAWCore.Name as SC
import qualified SAWCore.SharedTerm as SC
import qualified CryptolSAWCore.TypedTerm as SC
import qualified SAWCore.Recognizer as R

import qualified CryptolSAWCore.Cryptol as CSC

import qualified Cryptol.TypeCheck.Type as C

import SAWCentral.Yosys.Utils

newtype YosysImport = YosysImport { yosysImport :: Map Text SC.TypedTerm }

data YosysTheorem = YosysTheorem
  { _theoremURI :: URI.URI -- ^ URI identifying overridden module
  , _theoremInputCryptolType :: C.Type -- ^ cryptol type of r
  , _theoremOutputCryptolType :: C.Type -- ^ cryptol type of (module r)
  , _theoremInputType :: SC.Term -- ^ type of r
  , _theoremOutputType :: SC.Term -- ^ type of (module r)
  , _theoremModule :: SC.Term -- ^ {{ \r -> module r }}
  , _theoremPrecond :: Maybe SC.Term -- ^ {{ \r -> precond r }}
  , _theoremBody :: SC.Term -- ^ {{ \r -> other r }}
  } 
makeLenses ''YosysTheorem

-- | Construct a SAWCore proposition for the given theorem.
-- In pseudo-Cryptol, this looks like {{ \r -> precond r ==> (module r == body r) }}
theoremProp ::
  (MonadIO m, MonadThrow m) =>
  SC.SharedContext ->
  YosysTheorem ->
  m SC.TypedTerm
theoremProp sc thm = do
  r <- liftIO $ SC.scFreshVariable sc "r" $ thm ^. theoremInputType
  modr <- liftIO $ SC.scApply sc (thm ^. theoremModule) r
  bodyr <- liftIO $ SC.scApply sc (thm ^. theoremBody) r
  equality <- liftIO $ eqBvRecords sc (thm ^. theoremOutputCryptolType) modr bodyr
  res <- case thm ^. theoremPrecond of
    Nothing -> pure equality
    Just pc -> do
      pcr <- liftIO $ SC.scApply sc pc r
      liftIO $ SC.scImplies sc pcr equality
  func <- liftIO $ SC.scAbstractTerms sc [r] res
  let cty = C.tFun (thm ^. theoremInputCryptolType) C.tBit
  SC.TypedTerm (SC.TypedTermSchema $ C.tMono cty)
    <$> validateTerm sc
    ("constructing a proposition while verifying " <> URI.render (thm ^. theoremURI))
    func

-- | Construct a SAWCore proposition for the given theorem.
-- In pseudo-Cryptol, this looks like {{ \r -> if precond r then body r else module r }}
theoremReplacement ::
  (MonadIO m, MonadThrow m) =>
  SC.SharedContext ->
  YosysTheorem ->
  m SC.Term
theoremReplacement sc thm = do
  r <- liftIO $ SC.scFreshVariable sc "r" $ thm ^. theoremInputType
  body <- case thm ^. theoremPrecond of
    Nothing -> liftIO $ SC.scApply sc (thm ^. theoremBody) r
    Just pc -> do
      precond <- liftIO $ SC.scApply sc pc r
      thenCase <- liftIO $ SC.scApply sc (thm ^. theoremBody) r
      elseCase <- liftIO $ SC.scApply sc (thm ^. theoremModule) r
      liftIO $ SC.scIte sc (thm ^. theoremOutputType) precond thenCase elseCase
  ft <- liftIO $ SC.scAbstractTerms sc [r] body
  validateTerm sc
    ("constructing an override replacement for " <> URI.render (thm ^. theoremURI))
    ft

-- | Given a SAWCore term corresponding to an HDL module, a specification, and a precondition:
-- Construct a theorem summarizing the relationship between the module and the specification.
buildTheorem ::
  (MonadIO m, MonadThrow m) =>
  SC.SharedContext ->
  SC.TypedTerm ->
  SC.Term ->
  Maybe SC.TypedTerm ->
  SC.TypedTerm ->
  m YosysTheorem
buildTheorem sc ymod newmod precond body = do
  cty <- case SC.ttType ymod of
    SC.TypedTermSchema (C.Forall [] [] cty) -> pure cty
    _ -> throw YosysErrorInvalidOverrideTarget
  (cinpTy, coutTy) <- case cty of
    C.TCon (C.TC C.TCFun) [ci, co] -> pure (ci, co)
    _ -> throw YosysErrorInvalidOverrideTarget
  inpTy <- liftIO $ CSC.importType sc CSC.emptyEnv cinpTy
  outTy <- liftIO $ CSC.importType sc CSC.emptyEnv coutTy
  nmi <- case reduceSelectors (SC.ttTerm ymod) of
    (R.asConstant -> Just (SC.Name _ nmi)) -> pure nmi
    _ -> throw YosysErrorInvalidOverrideTarget
  uri <- case nmi of
    SC.ImportedName uri _ -> pure uri
    _ -> throw YosysErrorInvalidOverrideTarget
  pure YosysTheorem
    { _theoremURI = uri
    , _theoremInputCryptolType = cinpTy
    , _theoremOutputCryptolType = coutTy
    , _theoremInputType = inpTy
    , _theoremOutputType = outTy
    , _theoremModule = newmod
    , _theoremPrecond = SC.ttTerm <$> precond
    , _theoremBody = SC.ttTerm body
    }

-- | Reduce nested tuple and record selectors at the top-level of the
-- given term, if possible.
reduceSelectors :: SC.Term -> SC.Term
reduceSelectors t =
  case t of
    (R.asPairSelector -> Just (t1, b)) ->
      case R.asPairValue (reduceSelectors t1) of
        Nothing -> t
        Just (x, y) -> if b then y else x
    (R.asRecordSelector -> Just (t1, fname)) ->
      case R.asRecordValue (reduceSelectors t1) of
        Nothing -> t
        Just tm ->
          case Map.lookup fname tm of
            Nothing -> t
            Just t' -> t'
    _ -> t

-- | Applying a theorem thm as an "override" in a Yosys-derived term t proceeds as follows:
--  1) unfold all names except thm.theoremURI in t
--  2) traverse t, looking for constants named thm.theoremURI
--  4) replace the constant term with either thm.theoremBody, or
--     {{ \r -> if thm.theoremPrecond r then thm.theoremBody r else thm.theoremURI r }}
--     in the presence of a precondition
applyOverride ::
  forall m.
  (MonadIO m, MonadThrow m) =>
  SC.SharedContext ->
  YosysTheorem ->
  SC.Term ->
  m SC.Term
applyOverride sc thm t = do
  tidx <- liftIO (SC.scResolveNameByURI sc $ thm ^. theoremURI) >>= \case
    Nothing -> throw . YosysErrorOverrideNameNotFound . URI.render $ thm ^. theoremURI
    Just i -> pure i
  unfolded <- liftIO $ SC.scUnfoldConstantSet sc False (Set.singleton tidx) t
  cache <- liftIO SC.newCache
  let
    go :: SC.Term -> IO SC.Term
    go s@(SC.Unshared tf) = case tf of
      SC.Constant (SC.Name idx _)
        | idx == tidx -> theoremReplacement sc thm
        | otherwise -> pure s
      _ -> SC.Unshared <$> traverse go tf
    go s@SC.STApp { SC.stAppIndex = aidx, SC.stAppTermF = tf } = SC.useCache cache aidx $ case tf of
      SC.Constant (SC.Name idx _)
        | idx == tidx -> theoremReplacement sc thm
        | otherwise -> pure s
      _ -> SC.scTermF sc =<< traverse go tf
  ft <- liftIO $ go unfolded
  validateTerm sc
    ("applying an override for " <> URI.render (thm ^. theoremURI))
    ft
