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

import Data.Bifunctor (bimap)
import qualified Data.Maybe as Maybe
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
  { _cellStateInfoType :: SC.Term -- cell state type - either a bitvector for a $dff, or a record type
  , _cellStateInfoCryptolType :: C.Type -- cryptol type for the above
  , _cellStateInfoFields :: Maybe (Map Text (SC.Term, C.Type)) -- if the type is a record, the fields of the record
  }
makeLenses ''CellStateInfo

data TranslatedModule = TranslatedModule
  { _translatedModuleStateInfo :: Maybe CellStateInfo -- information about the state type for this module
  , _translatedModuleTerm :: SC.Term -- the lambda term for the output record (including state) in terms of the inputs (including state)
  }
makeLenses ''TranslatedModule

data TranslationContext m = TranslationContext
  { _translationContextModules :: Map ModuleName TranslatedModule
  , _translationContextStateTypes :: Map CellName CellStateInfo -- state type for every stateful cell in this module (including sequential submodules)
  , _translationContextPatternMap :: PatternMap m -- for each pattern, a term representing that pattern (parameterized by a function to get a term representing any other pattern)
  }
makeLenses ''TranslationContext

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
          let _cellStateInfoFields = Nothing
          pure $ Just CellStateInfo{..}
        _ -> pure Nothing

lookupStateFor ::
  forall m.
  MonadIO m =>
  SC.SharedContext ->
  Map CellName CellStateInfo -> -- state type info for each cell
  SC.Term -> -- record term mapping (zenc-ed) cell names to cell states
  CellName -> -- cell state to lookup
  m SC.Term
lookupStateFor sc states inpst cnm = do
  let fieldnm = cellIdentifier cnm
  cryptolRecordSelect sc (Map.mapKeys cellIdentifier states) inpst fieldnm

moduleInputPorts :: Module -> Map Text [Bitrep]
moduleInputPorts m =
  Map.fromList
  . Maybe.mapMaybe
  ( \(nm, ip) ->
      if ip ^. portDirection == DirectionInput || ip ^. portDirection == DirectionInout
      then Just (nm, ip ^. portBits)
      else Nothing
  )
  . Map.assocs
  $ m ^. modulePorts

moduleOutputPorts :: Module -> Map Text [Bitrep]
moduleOutputPorts m =
  Map.fromList
  . Maybe.mapMaybe
  ( \(nm, ip) ->
      if ip ^. portDirection == DirectionOutput || ip ^. portDirection == DirectionInout
      then Just (nm, ip ^. portBits)
      else Nothing
  )
  . Map.assocs
  $ m ^. modulePorts

cellInputConnections :: Cell [b] -> Map Text [b]
cellInputConnections c = Map.intersection (c ^. cellConnections) inp
  where
    inp = Map.filter (\d -> d == DirectionInput || d == DirectionInout) $ c ^. cellPortDirections

cellOutputConnections :: Ord b => Cell [b] -> Map Text [b]
cellOutputConnections c = Map.intersection (c ^. cellConnections) out
  where
    out = Map.filter (\d -> d == DirectionOutput || d == DirectionInout) $ c ^. cellPortDirections

buildPatternMap ::
  forall m.
  MonadIO m =>
  SC.SharedContext ->
  Map ModuleName TranslatedModule -> -- all previously-translated modules
  Map CellName CellStateInfo -> -- state type info for each cell
  SC.Term -> -- record term mapping inputs to terms (including a field __state__, a record mapping (zenc-ed) cell names to cell states)
  Module -> -- the module being translated
  m (PatternMap m)
buildPatternMap sc mods states inp m = do
  -- grab the __state__ field from the module inputs
  inpst <- cryptolRecordSelect sc (Map.insert "__state__" () $ () <$ moduleInputPorts m) inp "__state__"
  -- for each cell, construct a term for each output pattern, parameterized by a lookup function for other patterns
  ms <- forM (Map.toList $ m ^. moduleCells) $ \(cnm, c) -> do
    let inpPatterns = case c ^. cellType of
          "$dff" -> Map.empty -- exclude dff inputs - this breaks loops involving state
          _ -> cellInputConnections c
    let outPatterns = cellOutputConnections c
    let derivedOutPatterns = Map.elems outPatterns <> ((:[]) <$> mconcat (Map.elems outPatterns))

    let
      -- given a pattern lookup function, get all of the cell's inputs
      getInps :: (YosysBitvecConsumer -> Pattern -> m SC.Term) -> m (Map Text SC.Term)
      getInps lookupPattern = fmap Map.fromList . forM (Map.toList inpPatterns) $ \(inm, pat) ->
        (inm,) <$> lookupPattern (YosysBitvecConsumerCell cnm inm) pat

    -- build a function from the cell's inputs to the cell's outputs
    inpsToOuts <- case Map.lookup (c ^. cellType) mods of
      Just subm -> pure $ \inps -> do
        subinpst <- lookupStateFor sc states inpst cnm
        domainRec <- cryptolRecord sc $ Map.insert "__state__" subinpst inps
        codomainRec <- liftIO $ SC.scApply sc (subm ^. translatedModuleTerm) domainRec
        fmap (Just . Map.fromList) . forM (Map.toList outPatterns) $ \(onm, _opat) -> do
          (onm,) <$> cryptolRecordSelect sc (Map.insert "__state__" () $ () <$ outPatterns) codomainRec onm
      Nothing -> pure $ primCellToMap sc c
    let
      -- given a pattern lookup function build a map from output patterns to terms
      f :: (YosysBitvecConsumer -> Pattern -> m SC.Term) -> m (Map Pattern SC.Term)
      f = getInps >=> inpsToOuts >=> \case
        Nothing -> throw $ YosysErrorNoSuchCellType (c ^. cellType) cnm
        Just outs -> do
          ms <- forM (Map.toList outs) $ \(onm, otm) ->
            case Map.lookup onm $ c ^. cellConnections of
              Nothing -> panic "buildPatternMap" ["Missing expected output name for cell"]
              Just opat -> deriveTermsByIndices sc opat otm
          pure $ Map.unions ms

    -- for each output pattern, construct a function that takes a pattern lookup function and computes the associated term
    fmap Map.fromList . forM derivedOutPatterns $ \pat -> pure . (pat,) $ f >=> \pats -> do
      case Map.lookup pat pats of
        Nothing -> panic "buildPatternMap" ["Missing expected output pattern for cell"]
        Just t -> pure t
  -- all of the pattern term functions for all of the cells in the module
  pure $ Map.unions ms

buildTranslationContext ::
  MonadIO m =>
  SC.SharedContext ->
  Map ModuleName TranslatedModule -> -- previously translated modules
  SC.Term -> -- record term mapping (zenc-ed) cell names to cell states
  Module -> -- the module we're translating
  m (TranslationContext m)
buildTranslationContext sc mods inpst m = do 
  let _translationContextModules = mods
  _translationContextStateTypes <- buildTranslationContextStateTypes sc mods m
  _translationContextPatternMap <- buildPatternMap sc mods _translationContextStateTypes inpst m
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

translatePattern ::
  MonadIO m =>
  TranslationContext m ->
  YosysBitvecConsumer ->
  Pattern ->
  m SC.Term
translatePattern ctx c p = do
  let pmap = ctx ^. translationContextPatternMap
  case Map.lookup p pmap of
    Nothing -> throw $ YosysErrorNoSuchOutputBitvec (Text.pack $ show p) c
    Just f -> f $ translatePattern ctx

translateModule ::
  MonadIO m =>
  SC.SharedContext ->
  TranslationContext m ->
  Module ->
  m TranslatedModule
translateModule sc ctx m = do
  let states = ctx ^. translationContextStateTypes

  -- description of the state fields of the module
  _translatedModuleStateInfo <- if Map.null states
    then pure Nothing
    else do
    let fields = Map.fromList $ bimap cellIdentifier (\cs -> (cs ^. cellStateInfoType, cs ^. cellStateInfoCryptolType)) <$> Map.toList states
    ty <- fieldsToType sc fields
    cty <- fieldsToCryptolType fields 
    pure $ Just CellStateInfo
      { _cellStateInfoType = ty
      , _cellStateInfoCryptolType = cty
      , _cellStateInfoFields = Just fields
      }

  inpst <- _
  -- for each stateful cell, build a term representing the new state for that cell
  outst <- fmap Map.fromList . forM (Map.toList states) $ \(cnm, _cs) -> do
    case Map.lookup cnm (m ^. moduleCells) of
      Nothing -> panic "translateModule" ["Previously observed cell does not exist"]
      Just c -> case c ^. cellType of
        "$dff" -- if the cell is a $dff, the new state is just whatever is connected to the input
          | Just pat <- Map.lookup "D" (c ^. cellConnections) ->
              (cnm,) <$> translatePattern ctx (YosysBitvecConsumerCell cnm "D") pat
        _
          | Just subm <- Map.lookup (c ^. cellType) (ctx ^. translationContextModules) -> do
              -- otherwise, the cell is a stateful submodule: the new state is obtained from the submodules's update function applied to the inputs and old state
              inps <- _
              let outPatterns = _
              subinpst <- lookupStateFor sc states inpst cnm
              domainRec <- cryptolRecord sc $ Map.insert "__state__" subinpst inps
              codomainRec <- liftIO $ SC.scApply sc (subm ^. translatedModuleTerm) domainRec
              (cnm,) <$> cryptolRecordSelect sc (Map.insert "__state__" () $ () <$ outPatterns) codomainRec "__state__"
        _ -> panic "translateModule" ["Malformed stateful cell type"]
          
  -- for each module output, collect a term for the output
  outputs <- _

  _translatedModuleTerm <- _

  pure TranslatedModule{..}
