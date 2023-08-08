{- |
Module      : SAWScript.Yosys.CompositionalTranslation
Description : Translating Yosys modules into SAWCore terms
License     : BSD3
Maintainer  : sbreese
Stability   : experimental

This module implements a function 'translateModule' that, given a Yosys 'Module'
and a mapping from other module names to 'TranslatedModule's, produces a 'TranslatedModule'.
Lenses 'translatedModuleTerm', 'translatedModuleType', and 'translatedModuleCryptolType'
can be used to extract information from a 'TranslatedModule' (e.g. to build a 'TypedTerm').
The translation works for both combinational and sequential circuits.
-}

{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# Language TemplateHaskell #-}
{-# Language ConstraintKinds #-}
{-# Language FlexibleContexts #-}
{-# Language RecordWildCards #-}
{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}
{-# Language TupleSections #-}
{-# Language ScopedTypeVariables #-}
{-# Language ViewPatterns #-}

module SAWScript.Yosys.CompositionalTranslation
  ( TranslatedModule
  , translatedModuleTerm
  , translatedModuleType, translatedModuleCryptolType
  , translateModule
  ) where

import Control.Lens.TH (makeLenses)

import Control.Lens ((^.))
import Control.Monad (forM, (>=>), void)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import Data.Bifunctor (bimap)
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

type ModuleName = Text -- TODO: Is this right? Is a ModuleName just a CellTypeUserType? It kinda has to be this type for the whole thing to typecheck.
type CellName = Text
type Pattern = [Bitrep]
type PatternMap m = Map Pattern ((YosysBitvecConsumer -> Pattern -> m SC.Term) -> m SC.Term)

-- | Information about the state type of a particular cell
data CellStateInfo = CellStateInfo
  { _cellStateInfoType :: SC.Term -- ^ Cell state type - either a bitvector for a $dff, or a record type
  , _cellStateInfoCryptolType :: C.Type -- ^ Cryptol type for the above
  , _cellStateInfoFields :: Maybe (Map Text (SC.Term, C.Type)) -- ^ If the type is a record, the fields of the record
  }
makeLenses ''CellStateInfo

-- | The SAWCore representation and SAW/Cryptol type information of a hardware module
data TranslatedModule = TranslatedModule
  { _translatedModuleStateInfo :: Maybe CellStateInfo -- ^ Information about the state type for this module
  , _translatedModuleTerm :: SC.Term -- ^ The lambda term for the output record (including state) in terms of the inputs (including state)
  , _translatedModuleType :: SC.Term -- ^ The SAWCore type of that term
  , _translatedModuleCryptolType :: C.Type -- ^ The Cryptol type of that term
  }
makeLenses ''TranslatedModule

-- | Information needed when translating a module
data TranslationContext m = TranslationContext
  { _translationContextModules :: Map ModuleName TranslatedModule -- ^ Context of previously translated modules
  , _translationContextStateTypes :: Map CellName CellStateInfo -- ^ State information for every stateful cell in this module (including sequential submodules)
  , _translationContextPatternMap :: PatternMap m -- ^ For each pattern, a term representing that pattern (parameterized by a function to get a term representing any other pattern)
  }
makeLenses ''TranslationContext

-- | Given a module and the context of previously-translated modules, construct a mapping from cell names to state information
buildTranslationContextStateTypes ::
  MonadIO m =>
  SC.SharedContext ->
  Map ModuleName TranslatedModule ->
  Module ->
  m (Map CellName CellStateInfo)
buildTranslationContextStateTypes sc mods m = do
  fmap (Map.mapMaybe id) . forM (m ^. moduleCells) $ \c -> do
    case c ^. cellType of
      CellTypeUserType submoduleName ->
        case Map.lookup submoduleName mods of
          Just tm -> pure $ tm ^. translatedModuleStateInfo
          Nothing -> pure Nothing -- TODO: Should this be an error? I think it would just be "nothing" in the old version
      CellTypeDff | Just w <- length <$> Map.lookup "Q" (c ^. cellConnections) -> do
        _cellStateInfoType <- liftIO . SC.scBitvector sc $ fromIntegral w
        let _cellStateInfoCryptolType = C.tWord $ C.tNum w
        let _cellStateInfoFields = Nothing
        pure $ Just CellStateInfo{..}
      _ -> pure Nothing

-- | Fetch the actual state term for a cell name, given the term for the __state__ input and information about what stateful cells exist
lookupStateFor ::
  forall m.
  MonadIO m =>
  SC.SharedContext ->
  Map CellName CellStateInfo {- ^ State type info for each cell -} ->
  SC.Term {- ^ Record term mapping (zenc-ed) cell names to cell states -} ->
  CellName {- ^ Cell state to lookup -} ->
  m SC.Term
lookupStateFor sc states inpst cnm = do
  let fieldnm = cellIdentifier cnm
  cryptolRecordSelect sc (Map.mapKeys cellIdentifier states) inpst fieldnm

-- | Add a record-typed field named __states__ to the given mapping of field names to types.
insertStateField ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text (SC.Term, C.Type) {- ^ The field types of __states__ -} ->
  Map Text (SC.Term, C.Type) {- ^ The mapping to update -} ->
  m (Map Text (SC.Term, C.Type))
insertStateField sc stateFields fields = do
  stateRecordType <- fieldsToType sc stateFields
  stateRecordCryptolType <- fieldsToCryptolType stateFields
  pure $ Map.insert "__state__" (stateRecordType, stateRecordCryptolType) fields

-- | Construct a mapping from patterns to functions that construct terms for those patterns, given functions that construct terms for other patterns
-- We later "tie the knot" on this mapping given a few known patterns (e.g. module inputs and constants) to obtain actual terms for each pattern.
buildPatternMap ::
  forall m.
  MonadIO m =>
  SC.SharedContext ->
  Map ModuleName TranslatedModule {- ^ All previously-translated modules -} ->
  Map CellName CellStateInfo {- ^ State type info for each cell -} ->
  SC.Term {- ^ Record term mapping inputs to terms (including a field __state__, a record mapping (zenc-ed) cell names to cell states) -} ->
  Module {- ^ The module being translated -} ->
  m (PatternMap m)
buildPatternMap sc mods states inp m = do
  let inputPorts = moduleInputPorts m
  let inputFields = if Map.null states then void inputPorts else Map.insert "__state__" () $ void inputPorts

  -- obtain a term for each input port by looking up their names in the input record
  inpTerms <- forM (Map.assocs inputPorts) $ \(nm, pat) -> do
    t <- liftIO $ cryptolRecordSelect sc inputFields inp nm
    fmap (const . pure) <$> deriveTermsByIndices sc pat t

  -- grab the __state__ field from the input record
  minpst <- if Map.null states then pure Nothing else Just <$> cryptolRecordSelect sc inputFields inp "__state__"

  -- for each cell, construct a term for each output pattern, parameterized by a lookup function for other patterns
  ms <- forM (Map.toList $ m ^. moduleCells) $ \(cnm, c) -> do
    let inpPatterns = case c ^. cellType of
          CellTypeDff -> Map.empty -- exclude dff inputs - this breaks loops involving state
          _ -> cellInputConnections c
    let outPatterns = cellOutputConnections c
    let derivedOutPatterns = Map.elems outPatterns <> ((:[]) <$> mconcat (Map.elems outPatterns))

    let
      -- given a pattern lookup function, get all of the cell's inputs
      getInps :: (YosysBitvecConsumer -> Pattern -> m SC.Term) -> m (Map Text SC.Term)
      getInps lookupPattern = fmap Map.fromList . forM (Map.toList inpPatterns) $ \(inm, pat) ->
        (inm,) <$> lookupPattern (YosysBitvecConsumerCell cnm inm) pat

    -- build a function from the cell's inputs to the cell's outputs
    inpsToOuts <- case c ^. cellType of
      CellTypeUserType submoduleName ->
        case Map.lookup submoduleName mods of
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
          Nothing -> pure $ \_ -> pure Nothing -- TODO: Is this the right thing to do in this case? Looks like 'Nothing' is what primCellToMap would return for a CellTypeUserType, so this just skips the call. Seem reasonable?
      CellTypeDff | Just inpst <- minpst -> pure $ \_ -> do
        cst <- lookupStateFor sc states inpst cnm
        pure . Just $ Map.fromList
          [ ("Q", cst)
          ]
      _ -> pure $ primCellToMap sc c

    let
      -- given a pattern lookup function build a map from output patterns to terms
      f :: (YosysBitvecConsumer -> Pattern -> m SC.Term) -> m (Map Pattern SC.Term)
      f = getInps >=> inpsToOuts >=> \case
        Nothing -> throw $ YosysErrorNoSuchCellType (Text.pack (show (c ^. cellType))) cnm
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

-- | Given a translation context (consisting of the previously translated modules, state information, and pattern map),
-- lookup the term for a given pattern in the pattern map.
translatePattern ::
  MonadIO m =>
  SC.SharedContext ->
  TranslationContext m ->
  YosysBitvecConsumer {- ^ Source of this lookup (for error messages) -} ->
  Pattern {- ^ Pattern to look up -} ->
  m SC.Term
translatePattern sc ctx c p = do
  let pmap = ctx ^. translationContextPatternMap
  case Map.lookup p pmap of
    -- if we find the pattern directly, use it (recursively calling translatePattern if other lookups are necessary)
    Just f -> f $ translatePattern sc ctx
    -- otherwise, we look up each bit individually and concatenate to construct the term.
    -- this is not an optimal scheme (e.g. you can imagine patterns [1, 2] and [3, 4] being present and looking up [1, 2, 3, 4])
    -- but it works well enough for now, and I suspect the resulting term size is easy to rewrite away in most cases
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

-- ^ Given previously translated modules, translate a module.
-- (This is the exported interface to the functionality implemented here.)
translateModule ::
  MonadIO m =>
  SC.SharedContext ->
  Map ModuleName TranslatedModule {- ^ Context of previously-translated modules -} ->
  Module {- ^ Yosys module to translate -} ->
  m TranslatedModule
translateModule sc mods m = do
  -- gather information about the stateful cells of the module
  states <- buildTranslationContextStateTypes sc mods m
  let stateFields = Map.fromList $ bimap cellIdentifier (\cs -> (cs ^. cellStateInfoType, cs ^. cellStateInfoCryptolType)) <$> Map.toList states
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

  -- construct the module function's domain type (a record of all inputs, and optionally state)
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

  -- construct a fresh variable of that type (this will become the parameter to the module function)
  domainRecordEC <- liftIO $ SC.scFreshEC sc "input" domainRecordType
  domainRecord <- liftIO $ SC.scExtCns sc domainRecordEC

  -- construct a pattern map from that domain record
  pmap <- buildPatternMap sc mods states domainRecord m
  let ctx = TranslationContext
        { _translationContextModules = mods
        , _translationContextStateTypes = states
        , _translationContextPatternMap = pmap
        }

  -- if this module is stateful, grab the __state__ field from the domain record
  minpst <- if Map.null states then pure Nothing else Just <$> cryptolRecordSelect sc domainFields domainRecord "__state__"

  -- for each stateful cell, build a term representing the new state for that cell
  outstMap <- fmap Map.fromList . forM (Map.toList states) $ \(cnm, _cs) -> do
    case Map.lookup cnm (m ^. moduleCells) of
      Nothing -> panic "translateModule" ["Previously observed cell does not exist"]
      Just c -> case c ^. cellType of
        CellTypeDff -- if the cell is a $dff, the new state is just whatever is connected to the input
          | Just pat <- Map.lookup "D" (c ^. cellConnections) ->
              (cnm,) <$> translatePattern sc ctx (YosysBitvecConsumerCell cnm "D") pat
        CellTypeUserType submoduleName
          | Just subm <- Map.lookup submoduleName (ctx ^. translationContextModules) -> do
              -- otherwise, the cell is a stateful submodule: the new state is obtained from the submodules's update function applied to the inputs and old state
              let inpPatterns = cellInputConnections c
              -- lookup the term for each input to the cell
              inps <- fmap Map.fromList . forM (Map.toList inpPatterns) $ \(inm, pat) ->
                (inm,) <$> translatePattern sc ctx (YosysBitvecConsumerCell cnm inm) pat
              let outPatterns = cellOutputConnections c
              -- build a record containing all of the cell's inputs, and (if stateful) the appropriate state field
              sdomainFields <- case minpst of
                Nothing -> pure inps
                Just inpst -> do
                  subinpst <- lookupStateFor sc states inpst cnm
                  pure $ Map.insert "__state__" subinpst inps
              let scodomainFields = if Map.null states then void outPatterns else Map.insert "__state__" () $ void outPatterns
              sdomainRec <- cryptolRecord sc sdomainFields
              -- apply the cell's function to the domain record
              scodomainRec <- liftIO $ SC.scApply sc (subm ^. translatedModuleTerm) sdomainRec
              -- grab the state field from the codomain record
              (cellIdentifier cnm,) <$> cryptolRecordSelect sc scodomainFields scodomainRec "__state__"
        _ -> panic "translateModule" ["Malformed stateful cell type"]

  -- build a record for the new value of __state__
  outst <- cryptolRecord sc outstMap
          
  -- for each module output, collect a term for the output
  let outputPorts = moduleOutputPorts m
  outs <- fmap Map.fromList . forM (Map.toList outputPorts) $ \(onm, pat) ->
    (onm,) <$> translatePattern sc ctx (YosysBitvecConsumerOutputPort onm) pat

  -- construct the return value of the module
  codomainRecord <- cryptolRecord sc $ if Map.null states then outs else Map.insert "__state__" outst outs

  -- construct the module function's codomain type (a record of all outputs, and optionally state)
  -- (this is the type of codomainRecord)
  outputFields <- forM outputPorts $ \inp -> do
    ty <- liftIO . SC.scBitvector sc . fromIntegral $ length inp
    let cty = C.tWord . C.tNum $ length inp
    pure (ty, cty)
  codomainFields <- if Map.null states then pure outputFields else insertStateField sc stateFields outputFields
  codomainRecordType <- fieldsToType sc codomainFields
  codomainRecordCryptolType <- fieldsToCryptolType codomainFields

  -- abstract over the return value - this binds the free variable domainRecord with a lambda
  _translatedModuleTerm <- liftIO $ SC.scAbstractExts sc [domainRecordEC] codomainRecord
  -- the type of _translatedModuleTerm - a function from domainRecordType to codomainRecordType
  _translatedModuleType <- liftIO $ SC.scFun sc domainRecordType codomainRecordType
  -- the same type as a Cryptol type
  let _translatedModuleCryptolType = C.tFun domainRecordCryptolType codomainRecordCryptolType

  pure TranslatedModule{..}
