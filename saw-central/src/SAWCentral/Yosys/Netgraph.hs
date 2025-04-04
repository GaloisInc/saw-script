{- |
Module      : SAWScript.Yosys.Netgraph
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

module SAWScript.Yosys.Netgraph where

import Control.Lens.TH (makeLenses)

import Control.Lens (at, (^.))
import Control.Monad (forM, foldM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import qualified Data.Maybe as Maybe
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Graph as Graph

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.Name as SC

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.Utils.RecordMap as C

import SAWScript.Yosys.Utils
import SAWScript.Yosys.IR
import SAWScript.Yosys.Cell

cellToEdges :: (Ord b, Eq b) => Cell [b] -> [(b, [b])]
cellToEdges c = (, inputBits) <$> outputBits
  where
    inputBits = List.nub . mconcat . Map.elems $ cellInputConnections c
    outputBits = List.nub . mconcat . Map.elems $ cellOutputConnections c

--------------------------------------------------------------------------------
-- ** Building a network graph from a Yosys module

data Netgraph b = Netgraph
  { _netgraphGraph :: Graph.Graph
  , _netgraphNodeFromVertex :: Graph.Vertex -> ((Text, Cell [b]), b, [b])
  -- , _netgraphVertexFromKey :: Bitrep -> Maybe Graph.Vertex
  }
makeLenses ''Netgraph

moduleNetgraph :: Module -> Netgraph Bitrep
moduleNetgraph m =
  let
    bitsFromInputPorts :: [Bitrep]
    bitsFromInputPorts = (<> [BitrepZero, BitrepOne])
      . List.nub
      . mconcat
      . Maybe.mapMaybe
      ( \(_, p) ->
          case p ^. portDirection of
            DirectionInput -> Just $ p ^. portBits
            DirectionInout -> Just $ p ^. portBits
            _ -> Nothing
      )
      . Map.assocs
      $ m ^. modulePorts --
    cellToNodes :: (Text, Cell [Bitrep]) -> [((Text, Cell [Bitrep]), Bitrep, [Bitrep])]
    cellToNodes (nm, c)
      | c ^. cellType == CellTypeDff = ((nm, c), , []) <$> outputBits
      | c ^. cellType == CellTypeFf = ((nm, c), , []) <$> outputBits
      | otherwise = ((nm, c), , inputBits) <$> outputBits
      where
        inputBits :: [Bitrep]
        inputBits =
          filter (not . flip elem bitsFromInputPorts)
          . List.nub
          . mconcat
          . Maybe.mapMaybe
          ( \(p, bits) ->
              case c ^. cellPortDirections . at p of
                Just DirectionInput -> Just bits
                Just DirectionInout -> Just bits
                _ -> Nothing
          )
          . Map.assocs
          $ c ^. cellConnections
        outputBits :: [Bitrep]
        outputBits = List.nub
          . mconcat
          . Maybe.mapMaybe
          ( \(p, bits) ->
              case c ^. cellPortDirections . at p of
                Just DirectionOutput -> Just bits
                Just DirectionInout -> Just bits
                _ -> Nothing
          )
          . Map.assocs
          $ c ^. cellConnections
    nodes = concatMap cellToNodes . Map.assocs $ m ^. moduleCells
    (_netgraphGraph, _netgraphNodeFromVertex, _netgraphVertexFromKey)
      = Graph.graphFromEdges nodes
  in Netgraph{..}

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
      vecBits <- liftIO $ SC.scVector sc onety bits
      liftIO $ SC.scJoin sc many one boolty vecBits

-- | Given a netgraph and an initial map from bit patterns to terms, populate that map with terms
-- generated from the rest of the netgraph.
netgraphToTerms ::
  (MonadIO m, Ord b, Show b) =>
  SC.SharedContext ->
  Map Text ConvertedModule ->
  Netgraph b ->
  Map [b] SC.Term ->
  m (Map [b] SC.Term)
netgraphToTerms sc env ng inputs
  | length (Graph.scc $ ng ^. netgraphGraph) /= length (ng ^. netgraphGraph)
  = do
      throw $ YosysError "Network graph contains a cycle after splitting on DFFs; SAW does not currently support analysis of this circuit"
  | otherwise = do
      let sorted = reverseTopSort $ ng ^. netgraphGraph
      foldM
        ( \acc v -> do
            let ((cnm, c), _output, _deps) = ng ^. netgraphNodeFromVertex $ v
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
