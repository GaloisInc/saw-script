{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language MultiWayIf #-}
{-# Language ViewPatterns #-}
{-# Language TupleSections #-}
{-# Language ScopedTypeVariables #-}

module SAWScript.Yosys.State where

import Control.Lens ((^.))
import Control.Monad (forM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Graph as Graph

import qualified Verifier.SAW.SharedTerm as SC

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.Utils.RecordMap as C

import SAWScript.Panic (panic)

import SAWScript.Yosys.Utils
import SAWScript.Yosys.IR
import SAWScript.Yosys.Netgraph

--------------------------------------------------------------------------------
-- ** Bit identifiers qualified with the name of a module instance.
-- To ensure global uniqueness, since for sequential circuits we use one global
-- graph of cells to properly detect cycles where the breaking DFF is within a
-- submodule.

data QualBitrep
  = QualBitrepZero
  | QualBitrepOne
  | QualBitrepX
  | QualBitrepZ
  | QualBitrep Text Integer
  deriving (Show, Eq, Ord)

qualifyBitrep :: Text -> Bitrep -> QualBitrep
qualifyBitrep _ BitrepZero = QualBitrepZero
qualifyBitrep _ BitrepOne = QualBitrepOne
qualifyBitrep _ BitrepX = QualBitrepX
qualifyBitrep _ BitrepZ = QualBitrepZ
qualifyBitrep nm (Bitrep i) = QualBitrep nm i

--------------------------------------------------------------------------------
-- ** Constructing a graph of the entire circuit.

type CircgraphNode = (Cell [QualBitrep], QualBitrep, [QualBitrep])

rebindQualify :: Text -> Map [Bitrep] [QualBitrep] -> [Bitrep] -> [QualBitrep]
rebindQualify inm binds bits = case Map.lookup bits binds of
  Nothing -> qualifyBitrep inm <$> bits
  Just qbits -> qbits

moduleToInlineNetgraph :: forall m. MonadIO m => Map Text Module -> Module -> m (Netgraph QualBitrep)
moduleToInlineNetgraph mmap topm = do
  nodes <- go "top" Map.empty topm
  -- liftIO $ putStrLn $ unlines $ (\(c, out, inp) -> show (c ^. cellType, out, inp)) <$> nodes
  let (_netgraphGraph, _netgraphNodeFromVertex, _) = Graph.graphFromEdges nodes
  pure Netgraph{..}
  where
    go :: Text -> Map [Bitrep] [QualBitrep] -> Module -> m [CircgraphNode]
    go inm binds m = do
      fmap mconcat . forM (Map.assocs $ m ^. moduleCells) $ \(cnm, fmap (rebindQualify inm binds) -> c) -> do
        if
          | c ^. cellType == "$dff"
            -> pure $ (\(out, _inp) -> (c, out, [])) <$> cellToEdges c
          | Text.isPrefixOf "$" (c ^. cellType)
            -> pure $ (\(out, inp) -> (c, out, inp)) <$> cellToEdges c
          | Just subm <- Map.lookup (c ^. cellType) mmap
            -> do
              sbinds <- forM (Map.assocs $ subm ^. modulePorts) $ \(pnm, p) -> do
                case Map.lookup pnm (c ^. cellConnections) of
                  Nothing -> throw . YosysError $ mconcat
                    [ "Cell \"", cnm, "\" does not provide a connection for port \"", pnm, "\""
                    ]
                  Just cbits -> pure (p ^. portBits, cbits)
              liftIO $ putStrLn $ "Descending into: " <> Text.unpack (c ^. cellType) <> ", binds are " <> show sbinds
              subcells <- go (inm <> " " <> cnm) (Map.fromList sbinds) subm
              pure subcells
          | otherwise
            -> throw . YosysError $ "No definition for module: " <> (c ^. cellType)

findDffs ::
  Netgraph QualBitrep ->
  [Cell [QualBitrep]]
findDffs ng =
  filter (\c -> c ^. cellType == "$dff")
  . fmap (\v -> let (c, _, _) = ng ^. netgraphNodeFromVertex $ v in c)
  . Graph.vertices
  $ ng ^. netgraphGraph

convertModuleInline ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text Module ->
  Module ->
  m ConvertedModule
convertModuleInline sc mmap m = do
  ng <- moduleToInlineNetgraph mmap m

  let dffs = findDffs ng
  stateFields <- fmap Map.fromList . forM dffs $ \c ->
    case Map.lookup "Q" $ c ^. cellConnections of
      Nothing -> panic "convertModuleInline" ["Missing expected output name for $dff cell"]
      Just b -> do
        t <- liftIO . SC.scBitvector sc . fromIntegral $ length b
        let cty = C.tWord . C.tNum $ length b
        pure ("nm", (t, cty))
  stateRecordType <- cryptolRecordType sc $ fst <$> stateFields
  let stateRecordCryptolType = C.tRec . C.recordFromFields $ (\(cnm, (_, t)) -> (C.mkIdent cnm, t)) <$> Map.assocs stateFields

  let inputPorts = moduleInputPorts m
  let outputPorts = moduleOutputPorts m
  inputFields <- forM inputPorts $ \inp -> do
    liftIO . SC.scBitvector sc . fromIntegral $ length inp
  outputFields <- forM outputPorts $ \out -> do
    liftIO . SC.scBitvector sc . fromIntegral $ length out

  let domainFields = Map.insert "__state__" stateRecordType inputFields
  let codomainFields = Map.insert "__state__" stateRecordType outputFields

  domainRecordType <- cryptolRecordType sc domainFields
  codomainRecordType <- cryptolRecordType sc codomainFields
  domainRecordEC <- liftIO $ SC.scFreshEC sc "input" domainRecordType
  domainRecord <- liftIO $ SC.scExtCns sc domainRecordEC

  derivedInputs <- forM (Map.assocs inputPorts) $ \(nm, inp) -> do
    t <- liftIO $ cryptolRecordSelect sc domainFields domainRecord nm
    deriveTermsByIndices sc (qualifyBitrep "top" <$> inp) t

  preStateRecord <- liftIO $ cryptolRecordSelect sc domainFields domainRecord "__state__"
  derivedPreState <- forM dffs $ \c ->
    case Map.lookup "Q" $ c ^. cellConnections of
      Nothing -> panic "convertModuleInline" ["Missing expected output name for $dff cell"]
      Just b -> do
        t <- liftIO $ cryptolRecordSelect sc stateFields preStateRecord "nm"
        deriveTermsByIndices sc b t

  zeroTerm <- liftIO $ SC.scBvConst sc 1 0
  oneTerm <- liftIO $ SC.scBvConst sc 1 1
  let inputs = Map.unions $ mconcat
        [ [ Map.fromList
            [ ( [QualBitrepZero], zeroTerm)
            , ( [QualBitrepOne], oneTerm )
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
        pure ("nm", t)
  postStateRecord <- cryptolRecord sc $ Map.fromList postStateFields

  outputRecord <- cryptolRecord sc . Map.insert "__state__" postStateRecord =<< forM outputPorts
    (\out -> lookupPatternTerm sc (qualifyBitrep "top" <$> out) terms)

  t <- liftIO $ SC.scAbstractExts sc [domainRecordEC] outputRecord
  ty <- liftIO $ SC.scFun sc domainRecordType codomainRecordType

  let toCryptol (nm, rep) = (C.mkIdent nm, C.tWord . C.tNum $ length rep)
  let cty = C.tFun
        (C.tRec . C.recordFromFields . (("__state__", stateRecordCryptolType):) $ toCryptol <$> Map.assocs inputPorts)
        (C.tRec . C.recordFromFields . (("__state__", stateRecordCryptolType):) $ toCryptol <$> Map.assocs outputPorts)
  pure ConvertedModule
    { _convertedModuleTerm = t
    , _convertedModuleType = ty
    , _convertedModuleCryptolType = cty
    }
