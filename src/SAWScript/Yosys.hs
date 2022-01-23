{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language ViewPatterns #-}
{-# Language LambdaCase #-}
{-# Language TupleSections #-}

module SAWScript.Yosys
  ( YosysIR
  , yosys_load_file
  , yosys_compositional_extract
  ) where

import Control.Lens.TH (makeLenses)
import Control.Lens (at, view, (^.))

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
import qualified Verifier.SAW.TypedTerm as SC

import SAWScript.Panic (panic)
import SAWScript.Value
import SAWScript.Yosys.IR

--------------------------------------------------------------------------------
-- ** Building the module graph from Yosys IR

data Modgraph = Modgraph
  { _modgraphGraph :: Graph.Graph
  , _modgraphNodeFromVertex :: Graph.Vertex -> (Module, Text, [Text])
  , _modgraphVertexFromKey :: Text -> Maybe Graph.Vertex
  }
makeLenses ''Modgraph

yosysIRModgraph :: YosysIR -> Modgraph
yosysIRModgraph ir =
  let
    moduleToNode :: (Text, Module) -> (Module, Text, [Text])
    moduleToNode (nm, m) = (m, nm, deps)
      where
        deps = view cellType <$> Map.elems (m ^. moduleCells)
    nodes = moduleToNode <$> Map.assocs (ir ^. yosysModules)
    (_modgraphGraph, _modgraphNodeFromVertex, _modgraphVertexFromKey)
      = Graph.graphFromEdges nodes
  in Modgraph{..}

--------------------------------------------------------------------------------
-- ** Building a network graph from a Yosys module

data Netgraph = Netgraph
  { _netgraphGraph :: Graph.Graph
  , _netgraphNodeFromVertex :: Graph.Vertex -> (Cell, [Bitrep], [[Bitrep]])
  , _netgraphVertexFromKey :: [Bitrep] -> Maybe Graph.Vertex
  }
makeLenses ''Netgraph

cellInputConnections :: Cell -> Map Text [Bitrep]
cellInputConnections c = Map.intersection (c ^. cellConnections) inp
  where
    inp = Map.filter (\d -> d == DirectionInput || d == DirectionInout) $ c ^. cellPortDirections

cellOutputConnections :: Cell -> Map [Bitrep] Text
cellOutputConnections c = Map.fromList . fmap Tuple.swap . Map.toList $ Map.intersection (c ^. cellConnections) out
  where
    out = Map.filter (\d -> d == DirectionOutput || d == DirectionInout) $ c ^. cellPortDirections

moduleNetgraph :: Module -> Netgraph
moduleNetgraph m =
  let
    cellToNodes :: Cell -> [(Cell, [Bitrep], [[Bitrep]])]
    cellToNodes c = (c, , inputBits) <$> outputBits
      where
        inputBits = List.nub
          . Maybe.mapMaybe
          ( \(p, bits) ->
              case c ^. cellPortDirections . at p of
                Just DirectionInput -> Just bits
                Just DirectionInout -> Just bits
                _ -> Nothing
          )
          . Map.assocs
          $ c ^. cellConnections
        outputBits = List.nub
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

-- | Given a Yosys cell and a map of terms for its arguments, construct a term representing the output.
cellToTerm ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text SC.Term {- ^ Environment of user-defined cells -} ->
  Cell {- ^ Cell type -} ->
  Map Text SC.Term {- ^ Mapping of input names to input terms -} ->
  m SC.Term
cellToTerm sc env c args = case c ^. cellType of
  "$or" -> do
    w <- liftIO $ SC.scNat sc $ case Map.lookup "Y" $ c ^. cellConnections of
      Nothing -> panic "cellToTerm" ["Missing expected output name for $or cell"]
      Just bits -> fromIntegral $ length bits
    identity <- liftIO $ SC.scBvBool sc w =<< SC.scBool sc False
    res <- liftIO $ foldM (SC.scBvOr sc w) identity args
    liftIO . SC.scRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  "$and" -> do
    w <- liftIO $ SC.scNat sc $ case Map.lookup "Y" $ c ^. cellConnections of
      Nothing -> panic "cellToTerm" ["Missing expected output name for $and cell"]
      Just bits -> fromIntegral $ length bits
    identity <- liftIO $ SC.scBvBool sc w =<< SC.scBool sc True
    res <- liftIO $ foldM (SC.scBvAnd sc w) identity args
    liftIO . SC.scRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  (flip Map.lookup env -> Just term) -> do
    r <- liftIO $ SC.scRecord sc args
    liftIO $ SC.scApply sc term r
  ct -> throw . YosysError $ "Unknown cell type: " <> ct

-- | Given a bit pattern ([Bitrep]) and a term, construct a map associating that output pattern with
-- the term, and each bit of that pattern with the corresponding bit of the term.
deriveTermsByIndices :: MonadIO m => SC.SharedContext -> [Bitrep] -> SC.Term -> m (Map [Bitrep] SC.Term)
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

-- | Given a netgraph and an initial map from bit patterns to terms, populate that map with terms
-- generated from the rest of the netgraph.
netgraphToTerms ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text SC.Term ->
  Netgraph ->
  Map [Bitrep] SC.Term ->
  m (Map [Bitrep] SC.Term)
netgraphToTerms sc env ng inputs
  | length (Graph.components $ ng ^. netgraphGraph ) > 1
  = do
      liftIO . print  . Graph.transposeG $ ng ^. netgraphGraph
      liftIO $ print (Graph.components $ ng ^. netgraphGraph )
      throw $ YosysError "Network graph contains a cycle; SAW does not currently support analysis of sequential circuits."
  | otherwise = do
      let sorted = Graph.reverseTopSort $ ng ^. netgraphGraph
      foldM
        ( \acc v -> do
            let (c, out, inp) = ng ^. netgraphNodeFromVertex $ v
            args <- forM (cellInputConnections c) $ \i -> -- for each input bit pattern
              case Map.lookup i acc of
                Just t -> pure t -- if we can find that pattern exactly, great! use that term
                Nothing -> do -- otherwise, find each individual bit and append the terms
                  one <- liftIO $ SC.scNat sc 1
                  boolty <- liftIO $ SC.scBoolType sc
                  many <- liftIO . SC.scNat sc . fromIntegral $ length i
                  vecty <- liftIO $ SC.scVecType sc many boolty
                  bits <- case sequence $ flip Map.lookup acc . (:[]) <$> i of
                    Just bits -> pure bits
                    Nothing -> throw . YosysError $ "Failed to find output bitvec: " <> Text.pack (show i)
                  vecBits <- liftIO $ SC.scVector sc vecty bits
                  liftIO $ SC.scJoin sc many one boolty vecBits
            r <- cellToTerm sc env c args -- once we've built a term, insert it along with each of its bits
            ts <- forM (cellOutputConnections c) $ \o -> do
              t <- liftIO $ SC.scRecordSelect sc r o
              deriveTermsByIndices sc out t
            pure $ Map.union (Map.unions ts) acc
        )
        inputs
        sorted

moduleToTerm ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text SC.Term ->
  Module ->
  m SC.Term
moduleToTerm sc env m = do
  let ng = moduleNetgraph m
  let inputports = Maybe.mapMaybe
        ( \(nm, ip) ->
            if ip ^. portDirection == DirectionInput || ip ^. portDirection == DirectionInout
            then Just (nm, ip ^. portBits)
            else Nothing
        )
        . Map.assocs
        $ m ^. modulePorts
  let outputports = Maybe.mapMaybe
        ( \(nm, ip) ->
            if ip ^. portDirection == DirectionOutput || ip ^. portDirection == DirectionInout
            then Just (nm, ip ^. portBits)
            else Nothing
        )
        . Map.assocs
        $ m ^. modulePorts
  inputRecordType <- liftIO . SC.scRecordType sc =<< forM inputports
    (\(nm, inp) -> do
        tp <- liftIO . SC.scBitvector sc . fromIntegral $ length inp
        pure (nm, tp)
    )
  outputRecordType <- liftIO . SC.scRecordType sc =<< forM outputports
    (\(nm, out) -> do
        tp <- liftIO . SC.scBitvector sc . fromIntegral $ length out
        pure (nm, tp)
    )
  inputRecordEC <- liftIO $ SC.scFreshEC sc "input" inputRecordType
  inputRecord <- liftIO $ SC.scExtCns sc inputRecordEC
  derivedInputs <- forM inputports $ \(nm, inp) -> do
    t <- liftIO $ SC.scRecordSelect sc inputRecord nm
    deriveTermsByIndices sc inp t
  let inputs = Map.unions derivedInputs
  env <- netgraphToTerms sc env ng inputs
  outputRecord <- liftIO . SC.scRecord sc . Map.fromList =<< forM outputports
    (\(nm, out) -> do
        case Map.lookup out env of
          Nothing -> throw . YosysError $ "Failed to find module output bits: " <> Text.pack (show out)
          Just t -> pure (nm, t)
    )
  liftIO $ SC.scAbstractExts sc [inputRecordEC] outputRecord

-- | Given a Yosys IR and the name of a VHDL module, construct a SAWCore term for that module.
yosysIRToTerm ::
  MonadIO m =>
  SC.SharedContext ->
  YosysIR ->
  Text ->
  m SC.TypedTerm
yosysIRToTerm sc ir modnm = do
  let mg = yosysIRModgraph ir
  let sorted = Graph.reverseTopSort $ mg ^. modgraphGraph
  env <- foldM
    (\acc v -> do
        let (m, nm, _) = mg ^. modgraphNodeFromVertex $ v
        t <- moduleToTerm sc acc m
        pure $ Map.insert nm t acc
    )
    Map.empty
    sorted
  m <- case Map.lookup modnm env of
    Just m -> pure m
    Nothing -> throw . YosysError $ "Failed to find module: " <> modnm
  liftIO $ SC.mkTypedTerm sc m

--------------------------------------------------------------------------------
-- ** Functions visible from SAWScript REPL

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

yosys_load_file :: FilePath -> TopLevel YosysIR
yosys_load_file = loadYosysIR

yosys_compositional_extract :: YosysIR -> String -> [()] -> ProofScript () -> TopLevel SC.TypedTerm
yosys_compositional_extract ir modnm _lemmas _tactic = do
  sc <- getSharedContext
  yosysIRToTerm sc ir (Text.pack modnm)
