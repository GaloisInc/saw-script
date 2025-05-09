{- |
Module      : SAWCentral.Yosys.Netgraph
Description : Translating graphs of Yosys cells into SAWCore
License     : BSD3
Maintainer  : sbreese
Stability   : experimental
-}

{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language ViewPatterns #-}
{-# Language LambdaCase #-}
{-# Language MultiWayIf #-}
{-# Language TupleSections #-}
{-# Language ScopedTypeVariables #-}

module SAWCentral.Yosys.Netgraph where

import Control.Lens.TH (makeLenses)

import Control.Lens ((^.))
import Control.Monad (forM, foldM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import qualified Data.Maybe as Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Graph as Graph

import qualified SAWCore.SharedTerm as SC
import qualified SAWCore.Name as SC

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.Utils.RecordMap as C

import SAWCentral.Yosys.Utils
import SAWCentral.Yosys.IR
import SAWCentral.Yosys.Cell

--------------------------------------------------------------------------------
-- ** Building a network graph from a Yosys module

data Netgraph = Netgraph
  { _netgraphGraph :: Graph.Graph
  , _netgraphNodeFromVertex :: Graph.Vertex -> (Cell [Bitrep], Text, [Text])
  -- , _netgraphVertexFromKey :: Bitrep -> Maybe Graph.Vertex
  }
makeLenses ''Netgraph

moduleNetgraph :: Module -> Netgraph
moduleNetgraph m =
  let
    sources :: Map Bitrep Text
    sources =
      Map.fromList $
      [ (b, cname)
      | (cname, c) <- Map.assocs (m ^. moduleCells)
      , b <- concat (Map.elems (cellOutputConnections c)) ]

    cellDeps :: Cell [Bitrep] -> [Text]
    cellDeps c
      | c ^. cellType == CellTypeDff = []
      | c ^. cellType == CellTypeFf = []
      | otherwise =
        Set.toAscList $ Set.fromList $
        Maybe.mapMaybe (flip Map.lookup sources) $
        concat $ Map.elems $ cellInputConnections c

    nodes :: [(Cell [Bitrep], Text, [Text])]
    nodes = [ (c, cname, cellDeps c) | (cname, c) <- Map.assocs (m ^. moduleCells) ]

    (_netgraphGraph, _netgraphNodeFromVertex, _netgraphVertexFromKey) =
      Graph.graphFromEdges nodes
  in
    Netgraph{..}

--------------------------------------------------------------------------------
-- ** Building a SAWCore term from a network graph

data ConvertedModule = ConvertedModule
  { _convertedModuleTerm :: SC.Term
  , _convertedModuleType :: SC.Term
  , _convertedModuleCryptolType :: C.Type
  }
makeLenses ''ConvertedModule

lookupPatternTerm ::
  (MonadIO m, Ord b, Show b) =>
  SC.SharedContext ->
  YosysBitvecConsumer ->
  [b] ->
  Map [b] SC.Term ->
  m SC.Term
lookupPatternTerm sc loc pat ts =
  case Map.lookup pat ts of
    Just t -> pure t
    Nothing -> do
      one <- liftIO $ SC.scNat sc 1
      boolty <- liftIO $ SC.scBoolType sc
      many <- liftIO . SC.scNat sc . fromIntegral $ length pat
      onety <- liftIO $ SC.scBitvector sc 1
      bits <- forM pat $ \b -> do
        case Map.lookup [b] ts of
          Just t -> pure t
          Nothing -> throw $ YosysErrorNoSuchOutputBitvec (Text.pack $ show b) loc
      -- Yosys lists bits in little-endian order, while scVector expects big-endian, so reverse
      vecBits <- liftIO $ SC.scVector sc onety (reverse bits)
      liftIO $ SC.scJoin sc many one boolty vecBits

-- | Given a netgraph and an initial map from bit patterns to terms, populate that map with terms
-- generated from the rest of the netgraph.
netgraphToTerms ::
  (MonadIO m) =>
  SC.SharedContext ->
  Map Text ConvertedModule ->
  Netgraph ->
  Map [Bitrep] SC.Term ->
  m (Map [Bitrep] SC.Term)
netgraphToTerms sc env ng inputs
  | length (Graph.scc $ ng ^. netgraphGraph) /= length (ng ^. netgraphGraph)
  = do
      throw $ YosysError "Network graph contains a cycle after splitting on DFFs; SAW does not currently support analysis of this circuit"
  | otherwise = do
      let sorted = reverseTopSort $ ng ^. netgraphGraph
      foldM
        ( \acc v -> do
            let (c, cnm, _deps) = ng ^. netgraphNodeFromVertex $ v
            let outputFields = Map.filter (\d -> d == DirectionOutput || d == DirectionInout) $ c ^. cellPortDirections
            if
              -- special handling for $dff/$ff nodes - we read their /output/ from the inputs map, and later detect and write their /input/ to the state
              | c ^. cellType == CellTypeDff
              , Just dffout <- Map.lookup "Q" $ c ^. cellConnections -> do
                  r <- lookupPatternTerm sc (YosysBitvecConsumerCell cnm "Q") dffout acc
                  ts <- deriveTermsByIndices sc dffout r
                  pure $ Map.union ts acc
              | c ^. cellType == CellTypeFf
              , Just ffout <- Map.lookup "Q" $ c ^. cellConnections -> do
                  r <- lookupPatternTerm sc (YosysBitvecConsumerCell cnm "Q") ffout acc
                  ts <- deriveTermsByIndices sc ffout r
                  pure $ Map.union ts acc
              | otherwise -> do
                  args <- fmap Map.fromList . forM (Map.assocs $ cellInputConnections c) $ \(inm, i) -> do -- for each input bit pattern
                    -- if we can find that pattern exactly, great! use that term
                    -- otherwise, find each individual bit and append the terms
                    (inm,) <$> lookupPatternTerm sc (YosysBitvecConsumerCell cnm inm) i acc

                  r <- primCellToTerm sc c args >>= \case
                    Just r -> pure r
                    Nothing ->
                      let submoduleName = asUserType $ c ^. cellType in
                      case Map.lookup submoduleName env of
                        Just cm -> do
                          r <- cryptolRecord sc args
                          liftIO $ SC.scApply sc (cm ^. convertedModuleTerm) r
                        Nothing ->
                            throw $ YosysErrorNoSuchSubmodule  submoduleName cnm

                  -- once we've built a term, insert it along with each of its bits
                  ts <- forM (Map.assocs $ cellOutputConnections c) $ \(o, out) -> do
                    t <- cryptolRecordSelect sc outputFields r o
                    deriveTermsByIndices sc out t
                  pure $ Map.union (Map.unions ts) acc
        )
        inputs
        sorted

convertModule ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text ConvertedModule ->
  Module ->
  m ConvertedModule
convertModule sc env m = do
  let ng = moduleNetgraph m

  let inputPorts = moduleInputPorts m
  let outputPorts = moduleOutputPorts m

  inputFields <- forM inputPorts
    (\inp -> do
        liftIO . SC.scBitvector sc . fromIntegral $ length inp
    )
  outputFields <- forM outputPorts
    (\out -> do
        liftIO . SC.scBitvector sc . fromIntegral $ length out
    )
  inputRecordType <- cryptolRecordType sc inputFields
  outputRecordType <- cryptolRecordType sc outputFields
  inputRecordEC <- liftIO $ SC.scFreshEC sc "input" inputRecordType
  inputRecord <- liftIO $ SC.scExtCns sc inputRecordEC

  derivedInputs <- forM (Map.assocs inputPorts) $ \(nm, inp) -> do
    t <- liftIO $ cryptolRecordSelect sc inputFields inputRecord nm
    deriveTermsByIndices sc inp t

  zeroTerm <- liftIO $ SC.scBvConst sc 1 0
  oneTerm <- liftIO $ SC.scBvConst sc 1 1
  oneBitType <- liftIO $ SC.scBitvector sc 1
  xMsg <- liftIO $ SC.scString sc "Attempted to read X bit"
  xTerm <- liftIO $ SC.scGlobalApply sc (SC.mkIdent SC.preludeName "error") [oneBitType, xMsg]
  zMsg <- liftIO $ SC.scString sc "Attempted to read Z bit"
  zTerm <- liftIO $ SC.scGlobalApply sc (SC.mkIdent SC.preludeName "error") [oneBitType, zMsg]
  let inputs = Map.unions $ mconcat
        [ [ Map.fromList
            [ ( [BitrepZero], zeroTerm)
            , ( [BitrepOne], oneTerm )
            , ( [BitrepX], xTerm )
            , ( [BitrepZ], zTerm )
            ]
          ]
        , derivedInputs
        ]

  terms <- netgraphToTerms sc env ng inputs
  outputRecord <- cryptolRecord sc =<< mapForWithKeyM outputPorts
    (\onm out -> lookupPatternTerm sc (YosysBitvecConsumerOutputPort onm) out terms)

  t <- liftIO $ SC.scAbstractExts sc [inputRecordEC] outputRecord
  ty <- liftIO $ SC.scFun sc inputRecordType outputRecordType

  let toCryptol (nm, rep) = (C.mkIdent nm, C.tWord . C.tNum $ length rep)
  let cty = C.tFun
        (C.tRec . C.recordFromFields $ toCryptol <$> Map.assocs inputPorts)
        (C.tRec . C.recordFromFields $ toCryptol <$> Map.assocs outputPorts)
  pure ConvertedModule
    { _convertedModuleTerm = t
    , _convertedModuleType = ty
    , _convertedModuleCryptolType = cty
    }
