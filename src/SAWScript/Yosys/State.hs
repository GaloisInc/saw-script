{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language MultiWayIf #-}
{-# Language ViewPatterns #-}
{-# Language TupleSections #-}
{-# Language ScopedTypeVariables #-}

module SAWScript.Yosys.State where

import Control.Lens.TH (makeLenses)

import Control.Lens ((^.))
import Control.Monad (forM, foldM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import Data.Bifunctor (bimap)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Graph as Graph

import Numeric.Natural (Natural)

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedTerm as SC
import qualified Verifier.SAW.Name as SC

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.Utils.RecordMap as C

import SAWScript.Panic (panic)

import SAWScript.Yosys.Utils
import SAWScript.Yosys.IR
import SAWScript.Yosys.Netgraph

findDffs ::
  Netgraph Bitrep ->
  Map Text (Cell [Bitrep])
findDffs ng =
  Map.fromList
  . filter (\(_, c) -> c ^. cellType == "$dff")
  . fmap (\v -> let (n, _, _) = ng ^. netgraphNodeFromVertex $ v in n)
  . Graph.vertices
  $ ng ^. netgraphGraph

data YosysSequential = YosysSequential
  { _yosysSequentialTerm :: SC.TypedTerm
  , _yosysSequentialStateFields :: Map Text (SC.Term, C.Type)
  , _yosysSequentialInputFields :: Map Text (SC.Term, C.Type)
  , _yosysSequentialOutputFields :: Map Text (SC.Term, C.Type)
  , _yosysSequentialStateWidths :: Map Text Natural
  }
makeLenses ''YosysSequential

fieldsToType ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text (SC.Term, C.Type) ->
  m SC.Term
fieldsToType sc = cryptolRecordType sc . fmap fst

fieldsToCryptolType ::
  MonadIO m =>
  Map Text (SC.Term, C.Type) ->
  m C.Type
fieldsToCryptolType fields = pure . C.tRec . C.recordFromFields $ bimap C.mkIdent snd <$> Map.assocs fields

insertStateField ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text (SC.Term, C.Type) ->
  Map Text (SC.Term, C.Type) ->
  m (Map Text (SC.Term, C.Type))
insertStateField sc stateFields fields = do
  stateRecordType <- fieldsToType sc stateFields
  stateRecordCryptolType <- fieldsToCryptolType stateFields
  pure $ Map.insert "__state__" (stateRecordType, stateRecordCryptolType) fields

convertModuleInline ::
  MonadIO m =>
  SC.SharedContext ->
  Module ->
  m YosysSequential
convertModuleInline sc m = do
  let ng = moduleNetgraph m

  -- construct SAWCore and Cryptol types
  let dffs = findDffs ng

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

  zeroTerm <- liftIO $ SC.scBvConst sc 1 0
  oneTerm <- liftIO $ SC.scBvConst sc 1 1
  let inputs = Map.unions $ mconcat
        [ [ Map.fromList
            [ ( [BitrepZero], zeroTerm)
            , ( [BitrepOne], oneTerm )
            ]
          ]
        , derivedInputs
        , derivedPreState
        ]

  terms <- netgraphToTerms sc Map.empty ng inputs

  postStateFields <- forM dffs $ \c ->
    case Map.lookup "D" $ c ^. cellConnections of
      Nothing -> panic "convertModuleInline" ["Missing expected input name for $dff cell"]
      Just b -> do
        t <- lookupPatternTerm sc b terms
        pure t
  postStateRecord <- cryptolRecord sc postStateFields

  outputRecord <- cryptolRecord sc . Map.insert "__state__" postStateRecord =<< forM outputPorts
    (\out -> lookupPatternTerm sc out terms)

  -- construct result
  t <- liftIO $ SC.scAbstractExts sc [domainRecordEC] outputRecord
  -- ty <- liftIO $ SC.scFun sc domainRecordType codomainRecordType
  let cty = C.tFun domainCryptolRecordType codomainCryptolRecordType
  pure YosysSequential
    { _yosysSequentialTerm = SC.TypedTerm (SC.TypedTermSchema $ C.tMono cty) t
    , _yosysSequentialStateFields = stateFields
    , _yosysSequentialInputFields = inputFields
    , _yosysSequentialOutputFields = outputFields
    , _yosysSequentialStateWidths = stateWidths
    }

composeYosysSequential ::
  forall m.
  MonadIO m =>
  SC.SharedContext ->
  YosysSequential ->
  Integer ->
  m SC.TypedTerm
composeYosysSequential sc s n = do
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
  initialStateMsg <- liftIO $ SC.scString sc "Attempted to read initial state of sequential circuit"
  initialState <- liftIO $ SC.scGlobalApply sc (SC.mkIdent SC.preludeName "error") [stateType, initialStateMsg]
  -- initialStateFields <- forM (s ^. yosysSequentialStateWidths) $ \w -> do
  --   liftIO $ SC.scBvConst sc w 0
  -- initialState <- cryptolRecord sc initialStateFields
  (_, outputs) <- foldM (\acc i -> compose1 i acc) (initialState, Map.empty) [0..n]
  outputRecord <- cryptolRecord sc outputs
  res <- liftIO $ SC.scAbstractExts sc [extendedInputRecordEC] outputRecord
  let cty = C.tFun extendedInputCryptolType extendedOutputCryptolType
  pure $ SC.TypedTerm (SC.TypedTermSchema $ C.tMono cty) res
