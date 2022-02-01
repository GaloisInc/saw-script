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

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.Utils.RecordMap as C

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

cryptolRecordType ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text SC.Term ->
  m SC.Term
cryptolRecordType sc fields =
  liftIO $ SC.scTupleType sc (fmap snd . C.canonicalFields . C.recordFromFields $ Map.assocs fields)

cryptolRecord ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text SC.Term ->
  m SC.Term
cryptolRecord sc fields =
  liftIO $ SC.scTuple sc (fmap snd . C.canonicalFields . C.recordFromFields $ Map.assocs fields)

cryptolRecordSelect ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text a ->
  SC.Term ->
  Text ->
  m SC.Term
cryptolRecordSelect sc fields r nm =
  case List.elemIndex nm ord of
    Just i -> liftIO $ SC.scTupleSelector sc r (i + 1) (length ord)
    Nothing -> throw . YosysError $ mconcat
      [ "Could not build record selector term for field name \""
      , nm
      , "\" on record term: "
      , Text.pack $ show r
      , "\nFields are: "
      , Text.pack $ show $ Map.keys fields
      ]
  where ord = fmap fst . C.canonicalFields . C.recordFromFields $ Map.assocs fields

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
    cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  "$and" -> do
    w <- liftIO $ SC.scNat sc $ case Map.lookup "Y" $ c ^. cellConnections of
      Nothing -> panic "cellToTerm" ["Missing expected output name for $and cell"]
      Just bits -> fromIntegral $ length bits
    identity <- liftIO $ SC.scBvBool sc w =<< SC.scBool sc True
    res <- liftIO $ foldM (SC.scBvAnd sc w) identity args
    cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  (flip Map.lookup env -> Just term) -> do
    r <- cryptolRecord sc args
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
            let (c, out, _) = ng ^. netgraphNodeFromVertex $ v
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
            let fields = Map.filter (\d -> d == DirectionOutput || d == DirectionInout) $ c ^. cellPortDirections
            ts <- forM (cellOutputConnections c) $ \o -> do
              t <- cryptolRecordSelect sc fields r o
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
  m (SC.Term, SC.TypedTermType)
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
  inputRecordType <- cryptolRecordType sc . Map.fromList =<< forM inputports
    (\(nm, inp) -> do
        tp <- liftIO . SC.scBitvector sc . fromIntegral $ length inp
        pure (nm, tp)
    )
  inputRecordEC <- liftIO $ SC.scFreshEC sc "input" inputRecordType
  inputRecord <- liftIO $ SC.scExtCns sc inputRecordEC
  derivedInputs <- forM inputports $ \(nm, inp) -> do
    t <- liftIO $ cryptolRecordSelect sc (Map.fromList inputports) inputRecord nm
    deriveTermsByIndices sc inp t
  let inputs = Map.unions derivedInputs
  terms <- netgraphToTerms sc env ng inputs
  outputRecord <- cryptolRecord sc . Map.fromList =<< forM outputports
    (\(nm, out) -> do
        case Map.lookup out terms of
          Nothing -> throw . YosysError $ "Failed to find module output bits: " <> Text.pack (show out)
          Just t -> pure (nm, t)
    )
  t <- liftIO $ SC.scAbstractExts sc [inputRecordEC] outputRecord
  let toCryptol (nm, rep) = (C.mkIdent nm, C.tWord . C.tNum $ length rep)
  let cty = C.tFun
        (C.tRec . C.recordFromFields $ toCryptol <$> inputports)
        (C.tRec . C.recordFromFields $ toCryptol <$> outputports)
  pure (t, SC.TypedTermSchema $ C.tMono cty)

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
  (termEnv, typeEnv) <- foldM
    (\(termEnv, typeEnv) v -> do
        let (m, nm, _) = mg ^. modgraphNodeFromVertex $ v
        (t, schema) <- moduleToTerm sc termEnv m
        pure (Map.insert nm t termEnv, Map.insert nm schema typeEnv)
    )
    (Map.empty, Map.empty)
    sorted
  (m, schema) <- case (Map.lookup modnm termEnv, Map.lookup modnm typeEnv) of
    (Just m, Just schema) -> pure (m, schema)
    _ -> throw . YosysError $ "Failed to find module: " <> modnm
  pure $ SC.TypedTerm schema m

--------------------------------------------------------------------------------
-- ** Functions visible from SAWScript REPL

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

yosys_load_file :: FilePath -> TopLevel YosysIR
yosys_load_file = loadYosysIR

yosys_compositional_extract :: YosysIR -> String -> [()] -> ProofScript () -> TopLevel SC.TypedTerm
yosys_compositional_extract ir modnm _lemmas _tactic = do
  sc <- getSharedContext
  yosysIRToTerm sc ir (Text.pack modnm)
