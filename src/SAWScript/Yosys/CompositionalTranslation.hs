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
import Control.Lens ((^.))
import Control.Monad (forM, (>=>), void)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import Data.Bifunctor (bimap)
import qualified Data.Maybe as Maybe
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.Name as SC

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
  , _translatedModuleType :: SC.Term
  , _translatedModuleCryptolType :: C.Type
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

-- | Add a record-typed field named __states__ to the given mapping of field names to types.
insertStateField ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text (SC.Term, C.Type) {- ^ The field types of "__states__" -} ->
  Map Text (SC.Term, C.Type) {- ^ The mapping to update -} ->
  m (Map Text (SC.Term, C.Type))
insertStateField sc stateFields fields = do
  stateRecordType <- fieldsToType sc stateFields
  stateRecordCryptolType <- fieldsToCryptolType stateFields
  pure $ Map.insert "__state__" (stateRecordType, stateRecordCryptolType) fields

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
  let inputPorts = moduleInputPorts m
  let inputFields = if Map.null states then void inputPorts else Map.insert "__state__" () $ void inputPorts

  inpTerms <- forM (Map.assocs inputPorts) $ \(nm, pat) -> do
    t <- liftIO $ cryptolRecordSelect sc inputFields inp nm
    fmap (const . pure) <$> deriveTermsByIndices sc pat t

  -- grab the __state__ field from the module inputs
  minpst <- if Map.null states then pure Nothing else Just <$> cryptolRecordSelect sc inputFields inp "__state__"
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
        (domainFields, codomainFields) <- case (subm ^. translatedModuleStateInfo, minpst) of
          (Just _, Just inpst) -> do
            subinpst <- lookupStateFor sc states inpst cnm
            pure
              ( Map.insert "__state__" subinpst inps
              , Map.insert "__state__" () $ void outPatterns
              )
          _ -> pure (inps, void outPatterns)
        domainRec <- cryptolRecord sc domainFields
        codomainRec <- liftIO $ SC.scApply sc (subm ^. translatedModuleTerm) domainRec
        fmap (Just . Map.fromList) . forM (Map.toList outPatterns) $ \(onm, _opat) -> do
          (onm,) <$> cryptolRecordSelect sc codomainFields codomainRec onm
      Nothing -> case c ^. cellType of
        "$dff"
          | Just inpst <- minpst -> pure $ \_ -> do
              cst <- lookupStateFor sc states inpst cnm
              pure . Just $ Map.fromList
                [ ("Q", cst)
                ]
        _ -> pure $ primCellToMap sc c
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
  zeroTerm <- liftIO $ SC.scBvConst sc 1 0
  oneTerm <- liftIO $ SC.scBvConst sc 1 1
  oneBitType <- liftIO $ SC.scBitvector sc 1
  xMsg <- liftIO $ SC.scString sc "Attempted to read X bit"
  xTerm <- liftIO $ SC.scGlobalApply sc (SC.mkIdent SC.preludeName "error") [oneBitType, xMsg]
  zMsg <- liftIO $ SC.scString sc "Attempted to read Z bit"
  zTerm <- liftIO $ SC.scGlobalApply sc (SC.mkIdent SC.preludeName "error") [oneBitType, zMsg]
  pure . Map.unions $ mconcat
    [ ms
    , inpTerms
    , [ Map.fromList
        [ ( [BitrepZero], const $ pure zeroTerm)
        , ( [BitrepOne], const $ pure oneTerm )
        , ( [BitrepX], const $ pure xTerm )
        , ( [BitrepZ], const $ pure zTerm )
        ]
      ]
    ]

translatePattern ::
  MonadIO m =>
  SC.SharedContext ->
  TranslationContext m ->
  YosysBitvecConsumer ->
  Pattern ->
  m SC.Term
translatePattern sc ctx c p = do
  let pmap = ctx ^. translationContextPatternMap
  case Map.lookup p pmap of
    Just f -> f $ translatePattern sc ctx
    Nothing -> do
      one <- liftIO $ SC.scNat sc 1
      boolty <- liftIO $ SC.scBoolType sc
      many <- liftIO . SC.scNat sc . fromIntegral $ length p
      onety <- liftIO $ SC.scBitvector sc 1
      bits <- forM p $ \b -> do
        case Map.lookup [b] pmap of
          Just t -> t $ translatePattern sc ctx
          Nothing -> throw $ YosysErrorNoSuchOutputBitvec (Text.pack $ show b) c
      vecBits <- liftIO $ SC.scVector sc onety bits
      liftIO $ SC.scJoin sc many one boolty vecBits

translateModule ::
  MonadIO m =>
  SC.SharedContext ->
  Map ModuleName TranslatedModule ->
  Module ->
  m TranslatedModule
translateModule sc mods m = do
  states <- buildTranslationContextStateTypes sc mods m
  let stateFields = Map.fromList $ bimap cellIdentifier (\cs -> (cs ^. cellStateInfoType, cs ^. cellStateInfoCryptolType)) <$> Map.toList states

  -- description of the state fields of the module
  _translatedModuleStateInfo <- if Map.null states
    then pure Nothing
    else do
    ty <- fieldsToType sc stateFields
    cty <- fieldsToCryptolType stateFields
    pure $ Just CellStateInfo
      { _cellStateInfoType = ty
      , _cellStateInfoCryptolType = cty
      , _cellStateInfoFields = Just stateFields
      }

  let inputPorts = moduleInputPorts m
  inputFields <- forM inputPorts $ \inp -> do
    ty <- liftIO . SC.scBitvector sc . fromIntegral $ length inp
    let cty = C.tWord . C.tNum $ length inp
    pure (ty, cty)
  domainFields <- if Map.null states
    then pure inputFields
    else insertStateField sc stateFields inputFields
  domainRecordType <- fieldsToType sc domainFields
  domainRecordCryptolType <- fieldsToCryptolType domainFields
  domainRecordEC <- liftIO $ SC.scFreshEC sc "input" domainRecordType
  domainRecord <- liftIO $ SC.scExtCns sc domainRecordEC

  minpst <- if Map.null states then pure Nothing else Just <$> cryptolRecordSelect sc domainFields domainRecord "__state__"
  pmap <- buildPatternMap sc mods states domainRecord m
  let ctx = TranslationContext
        { _translationContextModules = mods
        , _translationContextStateTypes = states
        , _translationContextPatternMap = pmap
        }

  -- for each stateful cell, build a term representing the new state for that cell
  outstMap <- fmap Map.fromList . forM (Map.toList states) $ \(cnm, _cs) -> do
    case Map.lookup cnm (m ^. moduleCells) of
      Nothing -> panic "translateModule" ["Previously observed cell does not exist"]
      Just c -> case c ^. cellType of
        "$dff" -- if the cell is a $dff, the new state is just whatever is connected to the input
          | Just pat <- Map.lookup "D" (c ^. cellConnections) ->
              (cnm,) <$> translatePattern sc ctx (YosysBitvecConsumerCell cnm "D") pat
        _
          | Just subm <- Map.lookup (c ^. cellType) (ctx ^. translationContextModules) -> do
              -- otherwise, the cell is a stateful submodule: the new state is obtained from the submodules's update function applied to the inputs and old state
              let inpPatterns = cellInputConnections c
              inps <- fmap Map.fromList . forM (Map.toList inpPatterns) $ \(inm, pat) ->
                (inm,) <$> translatePattern sc ctx (YosysBitvecConsumerCell cnm inm) pat
              let outPatterns = cellOutputConnections c
              sdomainFields <- case minpst of
                Nothing -> pure inps
                Just inpst -> do
                  subinpst <- lookupStateFor sc states inpst cnm
                  pure $ Map.insert "__state__" subinpst inps
              let scodomainFields = if Map.null states then void outPatterns else Map.insert "__state__" () $ void outPatterns
              sdomainRec <- cryptolRecord sc sdomainFields
              scodomainRec <- liftIO $ SC.scApply sc (subm ^. translatedModuleTerm) sdomainRec
              (cellIdentifier cnm,) <$> cryptolRecordSelect sc scodomainFields scodomainRec "__state__"
        _ -> panic "translateModule" ["Malformed stateful cell type"]
  outst <- cryptolRecord sc outstMap
          
  -- for each module output, collect a term for the output
  let outputPorts = moduleOutputPorts m
  outs <- fmap Map.fromList . forM (Map.toList outputPorts) $ \(onm, pat) ->
    (onm,) <$> translatePattern sc ctx (YosysBitvecConsumerOutputPort onm) pat
  codomainRecord <- cryptolRecord sc $ if Map.null states then outs else Map.insert "__state__" outst outs
  outputFields <- forM outputPorts $ \inp -> do
    ty <- liftIO . SC.scBitvector sc . fromIntegral $ length inp
    let cty = C.tWord . C.tNum $ length inp
    pure (ty, cty)
  codomainFields <- if Map.null states then pure outputFields else insertStateField sc stateFields outputFields
  codomainRecordType <- fieldsToType sc codomainFields
  codomainRecordCryptolType <- fieldsToCryptolType codomainFields

  _translatedModuleTerm <- liftIO $ SC.scAbstractExts sc [domainRecordEC] codomainRecord
  _translatedModuleType <- liftIO $ SC.scFun sc domainRecordType codomainRecordType
  let _translatedModuleCryptolType = C.tFun domainRecordCryptolType codomainRecordCryptolType

  pure TranslatedModule{..}
