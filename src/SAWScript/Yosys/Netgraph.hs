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

import qualified Data.Tuple as Tuple
import qualified Data.Maybe as Maybe
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Graph as Graph

import qualified Verifier.SAW.SharedTerm as SC

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.Utils.RecordMap as C

import SAWScript.Yosys.Utils
import SAWScript.Yosys.IR
import SAWScript.Yosys.Cell

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

cellOutputConnections :: Ord b => Cell [b] -> Map [b] Text
cellOutputConnections c = Map.fromList . fmap Tuple.swap . Map.toList $ Map.intersection (c ^. cellConnections) out
  where
    out = Map.filter (\d -> d == DirectionOutput || d == DirectionInout) $ c ^. cellPortDirections

cellToEdges :: (Ord b, Eq b) => Cell [b] -> [(b, [b])]
cellToEdges c = (, inputBits) <$> outputBits
  where
    inputBits = List.nub . mconcat . Map.elems $ cellInputConnections c
    outputBits = List.nub . mconcat . Map.keys $ cellOutputConnections c

--------------------------------------------------------------------------------
-- ** Building a network graph from a Yosys module

data Netgraph b = Netgraph
  { _netgraphGraph :: Graph.Graph
  , _netgraphNodeFromVertex :: Graph.Vertex -> (Cell [b], b, [b])
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
    cellToNodes :: Cell [Bitrep] -> [(Cell [Bitrep], Bitrep, [Bitrep])]
    cellToNodes c
      | c ^. cellType == "$dff" = (c, , []) <$> outputBits
      | otherwise = (c, , inputBits) <$> outputBits
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
    nodes = concatMap cellToNodes . Map.elems $ m ^. moduleCells
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

-- | Given a bit pattern ([Bitrep]) and a term, construct a map associating that output pattern with
-- the term, and each bit of that pattern with the corresponding bit of the term.
deriveTermsByIndices :: (MonadIO m, Ord b) => SC.SharedContext -> [b] -> SC.Term -> m (Map [b] SC.Term)
deriveTermsByIndices sc rep t = do
  boolty <- liftIO $ SC.scBoolType sc
  telems <- forM [0..length rep] $ \index -> do
    tlen <- liftIO . SC.scNat sc . fromIntegral $ length rep
    idx <- liftIO . SC.scNat sc $ fromIntegral index
    bit <- liftIO $ SC.scAt sc tlen boolty t idx
    liftIO $ SC.scSingle sc boolty bit
  pure . Map.fromList $ mconcat
    [ [(rep, t)]
    , zip ((:[]) <$> rep) telems
    ]

lookupPatternTerm ::
  (MonadIO m, Ord b, Show b) =>
  SC.SharedContext ->
  [b] ->
  Map [b] SC.Term ->
  m SC.Term
lookupPatternTerm sc pat ts =
  case Map.lookup pat ts of
    Just t -> pure t
    Nothing -> do
      one <- liftIO $ SC.scNat sc 1
      boolty <- liftIO $ SC.scBoolType sc
      many <- liftIO . SC.scNat sc . fromIntegral $ length pat
      vecty <- liftIO $ SC.scVecType sc many boolty
      bits <- forM pat $ \b -> do
        case Map.lookup [b] ts of
          Just t -> pure t
          Nothing -> do
            throw . YosysError $ "Failed to find output bitvec: " <> Text.pack (show b)
      vecBits <- liftIO $ SC.scVector sc vecty bits
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
      let sorted = Graph.reverseTopSort $ ng ^. netgraphGraph
      foldM
        ( \acc v -> do
            let (c, _output, _deps) = ng ^. netgraphNodeFromVertex $ v
            let outputFields = Map.filter (\d -> d == DirectionOutput || d == DirectionInout) $ c ^. cellPortDirections
            if
              -- special handling for $dff nodes - we read their /output/ from the inputs map, and later detect and write their /input/ to the state
              | c ^. cellType == "$dff"
              , Just dffout <- Map.lookup "Q" $ c ^. cellConnections -> do
                  r <- lookupPatternTerm sc dffout acc
                  ts <- deriveTermsByIndices sc dffout r
                  pure $ Map.union ts acc
              | otherwise -> do
                  args <- forM (cellInputConnections c) $ \i -> do -- for each input bit pattern
                    -- if we can find that pattern exactly, great! use that term
                    -- otherwise, find each individual bit and append the terms
                    lookupPatternTerm sc i acc

                  r <- primCellToTerm sc c args >>= \case
                    Just r -> pure r
                    Nothing -> case Map.lookup (c ^. cellType) env of
                      Just cm -> do
                        r <- cryptolRecord sc args
                        liftIO $ SC.scApply sc (cm ^. convertedModuleTerm) r
                      Nothing -> throw . YosysError $ "No definition for module: " <> (c ^. cellType)

                  -- once we've built a term, insert it along with each of its bits
                  ts <- forM (Map.assocs $ cellOutputConnections c) $ \(out, o) -> do
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
  let inputs = Map.unions $ mconcat
        [ [ Map.fromList
            [ ( [BitrepZero], zeroTerm)
            , ( [BitrepOne], oneTerm )
            ]
          ]
        , derivedInputs
        ]

  terms <- netgraphToTerms sc env ng inputs
  outputRecord <- cryptolRecord sc =<< forM outputPorts
    (\out -> lookupPatternTerm sc out terms)

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
