{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module SAWScript.Yosys.Theorem where
 
import Control.Lens.TH (makeLenses)

import Control.Lens ((^.))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)
import Control.Monad.Catch (MonadThrow)

import qualified Data.Text as Text
import qualified Data.Set as Set

import qualified Text.URI as URI

import qualified Verifier.SAW.Cache as SC
import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedTerm as SC
import qualified Verifier.SAW.Recognizer as R

import qualified Verifier.SAW.Cryptol as CSC

import qualified Cryptol.TypeCheck.Type as C

import SAWScript.Yosys.Utils

data YosysTheorem = YosysTheorem
  { _theoremURI :: URI.URI -- URI identifying overridden module
  , _theoremInputCryptolType :: C.Type -- cryptol type of r
  , _theoremOutputCryptolType :: C.Type -- cryptol type of (module r)
  , _theoremInputType :: SC.Term -- type of r
  , _theoremOutputType :: SC.Term -- type of (module r)
  , _theoremModule :: SC.Term -- {{ \r -> module r }}
  , _theoremPrecond :: Maybe SC.Term -- {{ \r -> precond r }}
  , _theoremBody :: SC.Term -- {{ \r -> other r }}
  } 
makeLenses ''YosysTheorem

theoremProp ::
  (MonadIO m, MonadThrow m) =>
  SC.SharedContext ->
  YosysTheorem ->
  m SC.TypedTerm
theoremProp sc thm = do
  ec <- liftIO $ SC.scFreshEC sc "r" $ thm ^. theoremInputType
  r <- liftIO $ SC.scExtCns sc ec
  modr <- liftIO $ SC.scApply sc (thm ^. theoremModule) r
  bodyr <- liftIO $ SC.scApply sc (thm ^. theoremBody) r
  equality <- liftIO $ eqBvRecords sc (thm ^. theoremOutputCryptolType) modr bodyr
  res <- case thm ^. theoremPrecond of
    Nothing -> pure equality
    Just pc -> do
      pcr <- liftIO $ SC.scApply sc pc r
      liftIO $ SC.scImplies sc pcr equality
  func <- liftIO $ SC.scAbstractExts sc [ec] res
  let cty = C.tFun (thm ^. theoremInputCryptolType) C.tBit
  pure $ SC.TypedTerm (SC.TypedTermSchema $ C.tMono cty) func

theoremReplacement ::
  (MonadIO m, MonadThrow m) =>
  SC.SharedContext ->
  YosysTheorem ->
  m SC.Term
theoremReplacement sc thm = do
  ec <- liftIO $ SC.scFreshEC sc "r" $ thm ^. theoremInputType
  r <- liftIO $ SC.scExtCns sc ec
  body <- case thm ^. theoremPrecond of
    Nothing -> liftIO $ SC.scApply sc (thm ^. theoremBody) r
    Just pc -> do
      precond <- liftIO $ SC.scApply sc pc r
      thenCase <- liftIO $ SC.scApply sc (thm ^. theoremBody) r
      elseCase <- liftIO $ SC.scApply sc (thm ^. theoremModule) r
      liftIO $ SC.scIte sc (thm ^. theoremOutputType) precond thenCase elseCase
  liftIO $ SC.scAbstractExts sc [ec] body

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
    _ -> throw . YosysError $ mconcat
      [ "Term\n"
      , Text.pack . SC.showTerm $ SC.ttTerm ymod
      , "\ncannot be used as an override, as it does not have a monomorphic Cryptol type."
      ]
  (cinpTy, coutTy) <- case cty of
    C.TCon (C.TC C.TCFun) [ci, co] -> pure (ci, co)
    _ -> throw . YosysError $ mconcat
      [ "Term\n"
      , Text.pack . SC.showTerm $ SC.ttTerm ymod
      , "\ndoes not have a Cryptol function type."
      ]
  inpTy <- liftIO $ CSC.importType sc CSC.emptyEnv cinpTy
  outTy <- liftIO $ CSC.importType sc CSC.emptyEnv coutTy
  idx <- case SC.ttTerm ymod of
    (R.asConstant -> Just (SC.EC idx _ _, _)) -> pure idx
    _ -> throw . YosysError $ mconcat
      [ "Term\n"
      , Text.pack . SC.showTerm $ SC.ttTerm ymod
      , "\nis not a Yosys module."
      ]
  uri <- liftIO (SC.scLookupNameInfo sc idx) >>= \case
    Just (SC.ImportedName uri _) -> pure uri
    _ -> throw . YosysError $ mconcat
      [ "Term\n"
      , Text.pack . SC.showTerm $ SC.ttTerm ymod
      , "\ndoes not call a Yosys module on either side of an equality."
      ]
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

-- | Applying a theorem thm as an "override" in a Yosys-derived term t proceeds as follows:
--  1) unfold all names except thm.theoremURI in t
--  2) traverse t, looking for constants named thm.theoremURI
--  4) replace the constant term with either thm.theoremBody, or
--     {{ \x -> if thm.theoremPrecond r then thm.theoremBody else thm.theoremURI }}
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
    Nothing -> throw . YosysError $ "Could not resolve name " <> Text.pack (show $ thm ^. theoremURI)
    Just i -> pure i
  unfolded <- liftIO $ SC.scUnfoldConstantSet sc False (Set.singleton tidx) t
  cache <- liftIO SC.newCache
  let
    go :: SC.Term -> IO SC.Term
    go s@(SC.Unshared tf) = case tf of
      SC.Constant (SC.EC idx _ _) _
        | idx == tidx -> theoremReplacement sc thm
        | otherwise -> pure s
      _ -> SC.Unshared <$> traverse go tf
    go s@SC.STApp { SC.stAppIndex = aidx, SC.stAppTermF = tf } = SC.useCache cache aidx $ case tf of
      SC.Constant (SC.EC idx _ _) _
        | idx == tidx -> theoremReplacement sc thm
        | otherwise -> pure s
      _ -> SC.scTermF sc =<< traverse go tf
  liftIO $ go unfolded
