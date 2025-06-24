{- |
Module      : SAWCentral.Yosys.State
Description : Representing and manipulating stateful HDL circuits
License     : BSD3
Maintainer  : sbreese
Stability   : experimental
-}

{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language MultiWayIf #-}
{-# Language ViewPatterns #-}
{-# Language TupleSections #-}
{-# Language ScopedTypeVariables #-}

module SAWCentral.Yosys.State where

import Control.Lens.TH (makeLenses)

import Control.Lens ((^.))
import Control.Monad (forM, foldM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)

import Numeric.Natural (Natural)

import qualified SAWCore.SharedTerm as SC
import qualified CryptolSAWCore.TypedTerm as SC
import qualified SAWCore.Name as SC

import qualified Cryptol.TypeCheck.Type as C

import SAWCentral.Panic (panic)

import SAWCentral.Yosys.Utils
import SAWCentral.Yosys.IR
import SAWCentral.Yosys.Netgraph

-- | A SAWCore translation of an HDL module alongside some type
-- information that is useful to keep around.
data YosysSequential = YosysSequential
  { _yosysSequentialTerm :: SC.TypedTerm
    -- ^ The "raw" SAWCore term derived from the module, which
    -- includes a __state__ field in the input and output.
  , _yosysSequentialStateFields :: Map Text (SC.Term, C.Type)
    -- ^ A mapping from each state field name to a SAWCore and Cryptol type.
  , _yosysSequentialInputFields :: Map Text (SC.Term, C.Type)
    -- ^ A mapping from each input to a SAWCore and Cryptol type.
  , _yosysSequentialOutputFields :: Map Text (SC.Term, C.Type)
    -- ^ A mapping from each output to a SAWCore and Cryptol type.
  , _yosysSequentialInputWidths :: Map Text Natural
    -- ^ A mapping from each input to a width.
  , _yosysSequentialOutputWidths :: Map Text Natural
    -- ^ A mapping from each output to a width.
  , _yosysSequentialStateWidths :: Map Text Natural
    -- ^ A mapping from each state field to a width.
  }
makeLenses ''YosysSequential

-- | Add a record-typed field named __states__ to the given mapping of
-- field names to types.
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

-- | Translate a stateful HDL module into SAWCore
convertModuleInline ::
  MonadIO m =>
  SC.SharedContext ->
  Module ->
  m YosysSequential
convertModuleInline sc m = do
  let ng = moduleNetgraph m

  let netnames =
        Map.fromList
        [ (n ^. netnameBits, t)
        | (t, n) <- Map.assocs (m ^. moduleNetnames), not (n ^. netnameHideName) ]

  let bestName t c =
        fromMaybe (cellIdentifier t) $
        do bs <- Map.lookup "Q" (c ^. cellConnections)
           Map.lookup bs netnames

  -- construct SAWCore and Cryptol types
  let dffs =
        Map.fromList
        [ (bestName t c, c) | (t, c) <- Map.assocs (m ^. moduleCells), cellIsRegister c ]

  stateWidths <- forM dffs $ \c ->
    case Map.lookup "Q" $ c ^. cellConnections of
      Nothing -> panic "convertModuleInline" ["Missing expected output name for $dff cell"]
      Just b -> pure . fromIntegral $ length b

  stateFields <- forM stateWidths $ \w -> do
    t <- liftIO $ SC.scBitvector sc w
    let cty = C.tWord $ C.tNum w
    pure (t, cty)

  let inputPorts = moduleInputPorts m
  let outputPorts = moduleOutputPorts m
  inputFields <- forM inputPorts $ \inp -> do
    ty <- liftIO . SC.scBitvector sc . fromIntegral $ length inp
    let cty = C.tWord . C.tNum $ length inp
    pure (ty, cty)
  outputFields <- forM outputPorts $ \out -> do
    ty <- liftIO . SC.scBitvector sc . fromIntegral $ length out
    let cty = C.tWord . C.tNum $ length out
    pure (ty, cty)

  domainFields <- insertStateField sc stateFields inputFields
  codomainFields <- insertStateField sc stateFields outputFields

  domainRecordType <- fieldsToType sc domainFields
  domainCryptolRecordType <- fieldsToCryptolType domainFields
  -- codomainRecordType <- fieldsToType sc codomainFields
  codomainCryptolRecordType <- fieldsToCryptolType codomainFields

  -- convert module into term
  domainRecordEC <- liftIO $ SC.scFreshEC sc "input" domainRecordType
  domainRecord <- liftIO $ SC.scExtCns sc domainRecordEC

  derivedInputs <- forM (Map.assocs inputPorts) $ \(nm, inp) -> do
    t <- liftIO $ cryptolRecordSelect sc domainFields domainRecord nm
    deriveTermsByIndices sc inp t

  preStateRecord <- liftIO $ cryptolRecordSelect sc domainFields domainRecord "__state__"
  derivedPreState <- forM (Map.assocs dffs) $ \(cnm, c) ->
    case Map.lookup "Q" $ c ^. cellConnections of
      Nothing -> panic "convertModuleInline" ["Missing expected output name for $dff cell"]
      Just b -> do
        t <- liftIO $ cryptolRecordSelect sc stateFields preStateRecord cnm
        deriveTermsByIndices sc b t

  oneBitType <- liftIO $ SC.scBitvector sc 1
  xMsg <- liftIO $ SC.scString sc "Attempted to read X bit"
  xTerm <- liftIO $ SC.scGlobalApply sc (SC.mkIdent SC.preludeName "error") [oneBitType, xMsg]
  zMsg <- liftIO $ SC.scString sc "Attempted to read Z bit"
  zTerm <- liftIO $ SC.scGlobalApply sc (SC.mkIdent SC.preludeName "error") [oneBitType, zMsg]
  let inputs = Map.unions $ mconcat
        [ [ Map.fromList
            [ ( [BitrepZero], PretermBvNat 1 0 )
            , ( [BitrepOne], PretermBvNat 1 1 )
            , ( [BitrepX], PretermSlice 0 1 0 xTerm )
            , ( [BitrepZ], PretermSlice 0 1 0 zTerm )
            ]
          ]
        , derivedInputs
        , derivedPreState
        ]

  terms <- netgraphToTerms sc Map.empty ng inputs

  postStateFields <- mapForWithKeyM dffs $ \cnm c ->
    case Map.lookup "D" $ c ^. cellConnections of
      Nothing -> panic "convertModuleInline" ["Missing expected input name for $dff cell"]
      Just b -> do
        t <- lookupPatternTerm sc (YosysBitvecConsumerCell cnm "D") b terms
        pure t
  postStateRecord <- cryptolRecord sc postStateFields

  outputRecord <- cryptolRecord sc . Map.insert "__state__" postStateRecord =<< mapForWithKeyM outputPorts
    (\onm out -> lookupPatternTerm sc (YosysBitvecConsumerOutputPort onm) out terms)

  -- construct result
  t <- liftIO $ SC.scAbstractExts sc [domainRecordEC] outputRecord
  -- ty <- liftIO $ SC.scFun sc domainRecordType codomainRecordType
  _ <- validateTerm sc "translating a sequential circuit" t
  let cty = C.tFun domainCryptolRecordType codomainCryptolRecordType
  pure YosysSequential
    { _yosysSequentialTerm = SC.TypedTerm (SC.TypedTermSchema $ C.tMono cty) t
    , _yosysSequentialStateFields = stateFields
    , _yosysSequentialInputFields = inputFields
    , _yosysSequentialOutputFields = outputFields
    , _yosysSequentialInputWidths = fromIntegral . length <$> inputPorts
    , _yosysSequentialOutputWidths = fromIntegral . length <$> outputPorts
    , _yosysSequentialStateWidths = stateWidths
    }

-- | Given a SAWCore term with an explicit state, iterate the term the
-- given number of times. The resulting term has a parameter for the
-- initial state, the resulting Cryptol types does not.
composeYosysSequentialHelper ::
  forall m.
  MonadIO m =>
  SC.SharedContext ->
  YosysSequential ->
  Integer ->
  m (SC.Term, C.Type)
composeYosysSequentialHelper sc s n = do
  let t = SC.ttTerm $ s ^. yosysSequentialTerm

  width <- liftIO . SC.scNat sc $ fromIntegral n
  extendedInputFields <- forM (s ^. yosysSequentialInputFields) $ \(ty, cty) -> do
    exty <- liftIO $ SC.scVecType sc width ty
    let excty = C.tSeq (C.tNum n) cty
    pure (exty, excty)
  extendedOutputFields <- forM (s ^. yosysSequentialOutputFields) $ \(ty, cty) -> do
    exty <- liftIO $ SC.scVecType sc width ty
    let excty = C.tSeq (C.tNum n) cty
    pure (exty, excty)
  extendedInputType <- fieldsToType sc extendedInputFields
  extendedInputCryptolType <- fieldsToCryptolType extendedInputFields
  extendedInputRecordEC <- liftIO $ SC.scFreshEC sc "input" extendedInputType
  extendedInputRecord <- liftIO $ SC.scExtCns sc extendedInputRecordEC
  extendedOutputCryptolType <- fieldsToCryptolType extendedOutputFields

  allInputs <- fmap Map.fromList . forM (Map.keys extendedInputFields) $ \nm -> do
    inp <- liftIO $ cryptolRecordSelect sc extendedInputFields extendedInputRecord nm
    pure (nm, inp)

  codomainFields <- insertStateField sc (s ^. yosysSequentialStateFields) $ s ^. yosysSequentialOutputFields

  let
    buildIntermediateInput :: Integer -> SC.Term -> m SC.Term
    buildIntermediateInput i st = do
      inps <- fmap Map.fromList . forM (Map.assocs allInputs) $ \(nm, inp) -> do
        case Map.lookup nm $ s ^. yosysSequentialInputFields of
          Nothing -> throw . YosysError $ "Invalid input: " <> nm
          Just (elemty, _) -> do
            idx <- liftIO . SC.scNat sc $ fromIntegral i
            idxed <- liftIO $ SC.scAt sc width elemty inp idx
            pure (nm, idxed)
      let inpsWithSt = Map.insert "__state__" st inps
      cryptolRecord sc inpsWithSt

    summarizeOutput :: SC.Term -> m (SC.Term, Map Text SC.Term)
    summarizeOutput outrec = do
      outstate <- liftIO $ cryptolRecordSelect sc codomainFields outrec "__state__"
      outputs <- fmap Map.fromList . forM (Map.assocs $ s ^. yosysSequentialOutputFields) $ \(nm, (ty, _)) -> do
        out <- liftIO $ cryptolRecordSelect sc codomainFields outrec nm
        wrapped <- liftIO $ SC.scSingle sc ty out
        pure (nm, wrapped)
      pure (outstate, outputs)

    compose1 :: Integer -> (SC.Term, Map Text SC.Term) -> m (SC.Term, Map Text SC.Term)
    compose1 i (st, outs) = do
      inprec <- buildIntermediateInput i st
      outrec <- liftIO $ SC.scApply sc t inprec
      (st', outs') <- summarizeOutput outrec
      mergedOuts <- fmap Map.fromList . forM (Map.assocs outs') $ \(nm, arr) -> do
        case (Map.lookup nm $ s ^. yosysSequentialOutputFields, Map.lookup nm outs) of
          (Just (ty, _), Just rest) -> do
            restlen <- liftIO . SC.scNat sc $ fromIntegral i
            arrlen <- liftIO $ SC.scNat sc 1
            appended <- liftIO $ SC.scAppend sc restlen arrlen ty rest arr
            pure (nm, appended)
          _ -> pure (nm, arr)
      pure (st', mergedOuts)

  stateType <- fieldsToType sc $ s ^. yosysSequentialStateFields
  initialStateEC <- liftIO $ SC.scFreshEC sc "initial_state" stateType
  initialState <- liftIO $ SC.scExtCns sc initialStateEC
  (_, outputs) <- foldM (\acc i -> compose1 i acc) (initialState, Map.empty) [0..n]

  outputRecord <- cryptolRecord sc outputs
  res <- liftIO $ SC.scAbstractExts sc [initialStateEC, extendedInputRecordEC] outputRecord
  let cty = C.tFun extendedInputCryptolType extendedOutputCryptolType

  pure (res, cty)

-- | Given a SAWCore term with an explicit state, iterate the term the
-- given number of times. Accessing the initial state produces an
-- error.
composeYosysSequential ::
  forall m.
  MonadIO m =>
  SC.SharedContext ->
  YosysSequential ->
  Integer ->
  m SC.TypedTerm
composeYosysSequential sc s n = do
  (t, cty) <- composeYosysSequentialHelper sc s n
  stateType <- fieldsToType sc $ s ^. yosysSequentialStateFields
  initialStateMsg <- liftIO $ SC.scString sc "Attempted to read initial state of sequential circuit"
  initialState <- liftIO $ SC.scGlobalApply sc (SC.mkIdent SC.preludeName "error") [stateType, initialStateMsg]
  res <- liftIO $ SC.scApply sc t initialState
  pure $ SC.TypedTerm (SC.TypedTermSchema $ C.tMono cty) res

-- | Given a SAWCore term with an explicit state, iterate the term the
-- given number of times. The resulting term has a parameter for the
-- initial state.
composeYosysSequentialWithState ::
  forall m.
  MonadIO m =>
  SC.SharedContext ->
  YosysSequential ->
  Integer ->
  m SC.TypedTerm
composeYosysSequentialWithState sc s n = do
  (t, cty) <- composeYosysSequentialHelper sc s n
  scty <- fieldsToCryptolType $ s ^. yosysSequentialStateFields
  pure $ SC.TypedTerm (SC.TypedTermSchema . C.tMono $ C.tFun scty cty) t
