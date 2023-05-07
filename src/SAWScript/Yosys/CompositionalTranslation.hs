{-# Language TemplateHaskell #-}
{-# Language ConstraintKinds #-}
{-# Language FlexibleContexts #-}
{-# Language RecordWildCards #-}
{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}
{-# Language TupleSections #-}
{-# Language ScopedTypeVariables #-}
{-# Language ViewPatterns #-}

module SAWScript.Yosys.CompositionalTranslation where

import Control.Lens.TH (makeLenses)
import Control.Lens ((^.), view)
import Control.Monad (forM, (>=>))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader.Class (MonadReader(..))
import Control.Exception (Exception, throw)

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map

import Text.Encoding.Z (zEncodeString)

import qualified Verifier.SAW.SharedTerm as SC

import qualified Cryptol.TypeCheck.Type as C

import SAWScript.Panic (panic)

import SAWScript.Yosys.Utils
import SAWScript.Yosys.IR
import SAWScript.Yosys.Cell

type ModuleName = Text
type CellName = Text
type Pattern = [Bitrep]
type PatternMap m = Map Pattern ((YosysBitvecConsumer -> Pattern -> m SC.Term) -> m SC.Term)

data CellStateInfo = CellStateInfo
  { _cellStateInfoType :: SC.Term
  , _cellStateInfoCryptolType :: C.Type
  , _cellStateInfoFields :: Map Text (SC.Term, C.Type)
  }
makeLenses ''CellStateInfo

data TranslatedModule = TranslatedModule
  { _translatedModuleStateInfo :: Maybe CellStateInfo -- information about the state type for this module
  , _translatedModuleInputFields :: Map Text (SC.Term, C.Type)
  , _translatedModuleOutputFields :: Map Text (SC.Term, C.Type)
  , _translatedModuleTerm :: SC.Term -- the lambda term for the module
  , _translatedModuleType :: SC.Term -- the type of the module term
  , _translatedModuleCryptolType :: C.Type -- the cryptol type of the module term
  }
makeLenses ''TranslatedModule

data TranslationContext m = TranslationContext
  { _translationContextStateTypes :: Map CellName CellStateInfo -- state type for every stateful cell in this module (including sequential submodules)
  , _translationContextStateTerms :: Map Pattern SC.Term -- for all dff output bits in this module, the corresponding term
  , _translationContextPatternMap :: PatternMap m -- for each pattern, a term representing that pattern (parameterized by a function to get a term representing any other pattern)
  }
makeLenses ''TranslationContext

type Translating m =
  ( MonadIO m
  , MonadReader (TranslationContext m) m
  )

buildTranslationContextStateTypes ::
  MonadIO m =>
  SC.SharedContext ->
  Map ModuleName TranslatedModule ->
  Module ->
  m (Map CellName CellStateInfo)
buildTranslationContextStateTypes sc mods m = do
  fmap (Map.mapMaybe id) . forM (m ^. moduleCells) $ \c -> do
    case Map.lookup (c ^. cellType) mods of
      Just tm -> pure $ tm ^. translatedModuleStateInfo
      Nothing -> case c ^. cellType of
        "$dff" | Just w <- length <$> Map.lookup "Q" (c ^. cellConnections) -> do
          _cellStateInfoType <- liftIO . SC.scBitvector sc $ fromIntegral w
          let _cellStateInfoCryptolType = C.tWord $ C.tNum w
          pure $ Just CellStateInfo{..}
        _ -> pure Nothing

buildTranslationContextStateTerms ::
  MonadIO m =>
  SC.SharedContext ->
  SC.Term -> -- record term mapping (zenc-ed) cell names to cell states
  Map CellName CellStateInfo -> -- state type info for each cell
  Module ->
  m (Map Pattern SC.Term)
buildTranslationContextStateTerms sc inpst states m = do
  ms <- forM (Map.toList $ m ^. moduleCells) $ \(cnm, c) -> do
    case c ^. cellType of
      "$dff" | Just rep <- Map.lookup "Q" (c ^. cellConnections) -> do
        let fieldnm = cellIdentifier cnm
        st <- cryptolRecordSelect sc (Map.mapKeys cellIdentifier states) inpst fieldnm
        deriveTermsByIndices sc rep st
      _ -> pure Map.empty 
  pure $ Map.unions ms

buildPatternMap ::
  forall m.
  MonadIO m =>
  SC.SharedContext ->
  Map ModuleName TranslatedModule ->
  Map CellName CellStateInfo -> -- state type info for each cell
  Map Pattern SC.Term -> -- term for each dff output pattern
  Module ->
  m (PatternMap m)
buildPatternMap sc mods states terms m = do
  ms <- forM (Map.toList $ m ^. moduleCells) $ \(cnm, c) -> do
    inpPatterns <- undefined
    outPatterns <- undefined
    let
      getInps :: (YosysBitvecConsumer -> Pattern -> m SC.Term) -> m (Map Text SC.Term)
      getInps lookupPattern = fmap Map.fromList . forM (Map.toList inpPatterns) $ \(inm, pat) ->
        (inm,) <$> lookupPattern (YosysBitvecConsumerCell cnm inm) pat
    inpsToOuts <- case Map.lookup cnm mods of
      Just subm -> pure $ \inps -> do
        inpst <- undefined
        domainRec <- cryptolRecord sc $ Map.insert "__state__" inpst inps
        codomainRec <- liftIO $ SC.scApply sc (subm ^. translatedModuleTerm) domainRec
        fmap (Just . Map.fromList) . forM (Map.toList $ subm ^. translatedModuleOutputFields) $ \(onm, oty) -> do
          undefined
      Nothing -> pure (primCellToMap sc c)
    let
      f :: (YosysBitvecConsumer -> Pattern -> m SC.Term) -> m (Map Pattern SC.Term)
      f = getInps >=> inpsToOuts >=> \case
        Nothing -> throw $ YosysErrorNoSuchCellType (c ^. cellType) cnm
        Just outs -> do
          ms <- forM (Map.toList outs) $ \(onm, otm) ->
            case Map.lookup onm $ c ^. cellConnections of
              Nothing -> panic "buildPatternMap" ["Missing expected output name for cell"]
              Just opat -> deriveTermsByIndices sc opat otm
          pure $ Map.unions ms
    forM outPatterns $ \pat -> pure $ \lookupPattern -> f lookupPattern >>= \pats -> do
      case Map.lookup pat pats of
        Nothing -> panic "buildPatternMap" ["Missing expected output pattern for cell"]
        Just t -> pure t
  pure $ Map.unions ms

buildTranslationContext ::
  MonadIO m =>
  SC.SharedContext ->
  Map ModuleName TranslatedModule -> -- previously translated modules
  SC.Term -> -- record term mapping (zenc-ed) cell names to cell states
  Module -> -- the module we're translating
  m (TranslationContext m)
buildTranslationContext sc mods inpst m = do 
  _translationContextStateTypes <- buildTranslationContextStateTypes sc mods m
  _translationContextStateTerms <- buildTranslationContextStateTerms sc inpst _translationContextStateTypes m
  _translationContextPatternMap <- buildPatternMap sc mods _translationContextStateTypes _translationContextStateTerms m
  pure TranslationContext{..}

-- new approach:
--  iterate over entire module, find all dffs and stateful submodules
--  build state type for module. create parameter term for that type.
--  instantiate map from state patterns to lookups in state parameter term
--  we would like to build the term "top-down" from the outputs.
--  however, this is somewhat tricky, since it isn't immediately apparent where different bits in patterns come from.
--  instead we build an intermediate data structure: a mapping from patterns to functions that construct the corresponding term by recursively calling the translator
--  i.e., `pmap = Map Pattern ((Pattern -> IO Term) -> IO Term)`
--  the function Pattern -> IO Term is then `translate p = lookup p pmap >>= \f -> f translate`

translate ::
  Translating m =>
  YosysBitvecConsumer ->
  Pattern ->
  m SC.Term
translate c p = do
  pmap <- view translationContextPatternMap
  case Map.lookup p pmap of
    Nothing -> throw $ YosysErrorNoSuchOutputBitvec (Text.pack $ show p) c
    Just f -> f translate
