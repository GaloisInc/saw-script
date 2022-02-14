{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}
{-# Language ScopedTypeVariables #-}

module SAWScript.Yosys.Theorem where
 
import Control.Lens.TH (makeLenses)

import Control.Lens ((^.))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import qualified Data.Text as Text
import qualified Data.Set as Set

import qualified Text.URI as URI

import qualified Verifier.SAW.Cache as SC
import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedTerm as SC

import SAWScript.Yosys.IR

-- | A YosysTheorem is extracted from a term with the form:
-- {{ \r -> precond r ==> module r == other r }}
-- where "module" is a term derived from some Yosys module, "other" is a term of
-- appropriate type, and "precond" is an optional precondition for the equality.
data YosysTheorem = YosysTheorem
  { _theoremTerm :: SC.TypedTerm -- original term
  , _theoremURI :: URI.URI -- URI identifying overridden module
  , _theoremInputType :: SC.Term -- type of r
  , _theoremOutputType :: SC.Term -- type of (module r)
  , _theoremPrecond :: Maybe SC.Term -- {{ \r -> precond r }}
  , _theoremBody :: SC.Term -- {{ \r -> other r }}
  } 
makeLenses ''YosysTheorem

-- | Applying a theorem thm as an "override" in a Yosys-derived term t proceeds as follows:
--  1) unfold all names except thm.theoremURI in t
--  2) traverse t, looking for constants named thm.theoremURI
--  4) replace the constant term with either thm.theoremBody, or
--     {{ \x -> if thm.theoremPrecond r then thm.theoremBody else thm.theoremURI }}
--     in the presence of a precondition
rewriteWithTheorem ::
  forall m.
  MonadIO m =>
  SC.SharedContext ->
  YosysTheorem ->
  SC.Term ->
  m SC.Term
rewriteWithTheorem sc thm t = do
  tidx <- liftIO (SC.scResolveNameByURI sc $ thm ^. theoremURI) >>= \case
    Nothing -> throw . YosysError $ "Could not resolve name " <> Text.pack (show $ thm ^. theoremURI)
    Just i -> pure i
  unfolded <- liftIO $ SC.scUnfoldConstantSet sc False (Set.singleton tidx) t
  cache <- liftIO SC.newCache
  let
    thmMux :: SC.Term -> IO SC.Term
    thmMux elseCase =
      case thm ^. theoremPrecond of
        Just pc -> do
          -- build function term accepting a record of appropriate type
          -- body is: if thm.precond then thm.cellterm else def
          ec <- SC.scFreshEC sc "r" $ thm ^. theoremInputType
          r <- SC.scExtCns sc ec
          precond <- SC.scApply sc pc r
          thenCase <- SC.scApply sc (thm ^. theoremBody) r
          body <- SC.scIte sc (thm ^. theoremOutputType) precond thenCase elseCase
          SC.scAbstractExts sc [ec] body
        Nothing -> pure $ thm ^. theoremBody
    go :: SC.Term -> IO SC.Term
    go s@(SC.Unshared tf) = case tf of
      SC.Constant (SC.EC idx _ _) _
        | idx == tidx -> thmMux s
        | otherwise -> pure s
      _ -> SC.Unshared <$> traverse go tf
    go s@SC.STApp { SC.stAppIndex = aidx, SC.stAppTermF = tf } = SC.useCache cache aidx $ case tf of
      SC.Constant (SC.EC idx _ _) _
        | idx == tidx -> thmMux s
        | otherwise -> pure s
      _ -> SC.scTermF sc =<< traverse go tf
  liftIO $ go unfolded
