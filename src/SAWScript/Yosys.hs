{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language ViewPatterns #-}
{-# Language LambdaCase #-}
{-# Language TupleSections #-}
{-# Language ScopedTypeVariables #-}

module SAWScript.Yosys
  ( YosysIR
  , yosys_import
  ) where

import Control.Lens.TH (makeLenses)

import Control.Lens (at, view, (^.))
import Control.Monad (forM, foldM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

import Data.Bifunctor (first)
import qualified Data.Tuple as Tuple
import qualified Data.Maybe as Maybe
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import qualified Data.List.NonEmpty as NE
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Graph as Graph

import qualified Text.URI as URI

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedTerm as SC
import qualified Verifier.SAW.Name as SC

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
  -- , _modgraphVertexFromKey :: Text -> Maybe Graph.Vertex
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
  -- , _netgraphVertexFromKey :: [Bitrep] -> Maybe Graph.Vertex
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
  forall m.
  MonadIO m =>
  SC.SharedContext ->
  Map Text SC.Term {- ^ Environment of user-defined cells -} ->
  Cell {- ^ Cell type -} ->
  Map Text SC.Term {- ^ Mapping of input names to input terms -} ->
  m SC.Term
cellToTerm sc env c args = case c ^. cellType of
  "$not" -> bvUnaryOp $ SC.scBvNot sc
  "$pos" -> input "A"
  "$neg" -> bvUnaryOp $ SC.scBvNeg sc
  "$and" -> bvNAryOp $ SC.scBvAnd sc
  "$or" -> bvNAryOp $ SC.scBvOr sc
  "$xor" -> bvNAryOp $ SC.scBvXor sc
  "$xnor" -> bvNAryOp $ \w x y -> do
    r <- SC.scBvXor sc w x y
    SC.scBvNot sc w r
  "$reduce_and" -> bvReduce True =<< do
    liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "and"
  "$reduce_or" -> bvReduce False =<< do
    liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "or"
  "$reduce_xor" -> bvReduce False =<< do
    liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "xor"
  "$reduce_xnor" -> bvReduce True =<< do
    boolTy <- liftIO $ SC.scBoolType sc
    xEC <- liftIO $ SC.scFreshEC sc "x" boolTy
    x <- liftIO $ SC.scExtCns sc xEC
    yEC <- liftIO $ SC.scFreshEC sc "y" boolTy
    y <- liftIO $ SC.scExtCns sc yEC
    r <- liftIO $ SC.scXor sc x y
    res <- liftIO $ SC.scNot sc r
    liftIO $ SC.scAbstractExts sc [xEC, yEC] res
  "$reduce_bool" -> bvReduce False =<< do
    liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "or"
  "$shl" -> bvBinaryOp $ SC.scBvShl sc
  "$shr" -> bvBinaryOp $ SC.scBvShr sc
  "$sshl" -> bvBinaryOp $ SC.scBvShl sc -- same as shl
  "$sshr" -> bvBinaryOp $ SC.scBvSShr sc
  -- "$shift" -> _
  -- "$shiftx" -> _
  "$lt" -> bvBinaryOp $ SC.scBvULt sc
  "$le" -> bvBinaryOp $ SC.scBvULe sc
  "$gt" -> bvBinaryOp $ SC.scBvUGt sc
  "$ge" -> bvBinaryOp $ SC.scBvUGe sc
  "$eq" -> bvBinaryOp $ SC.scBvEq sc
  "$ne" -> bvBinaryOp $ \w x y -> do
    r <- SC.scBvEq sc w x y
    SC.scNot sc r
  "$eqx" -> bvBinaryOp $ SC.scBvEq sc
  "$nex" -> bvBinaryOp $ \w x y -> do
    r <- SC.scBvEq sc w x y
    SC.scNot sc r
  "$add" -> bvNAryOp $ SC.scBvAdd sc
  "$sub" -> bvBinaryOp $ SC.scBvSub sc
  "$mul" -> bvNAryOp $ SC.scBvMul sc
  "$div" -> bvBinaryOp $ SC.scBvUDiv sc
  "$mod" -> bvBinaryOp $ SC.scBvURem sc
  -- "$modfloor" -> _
  "$logic_not" -> do
    w <- outputWidth
    ta <- input "A"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    liftIO $ SC.scNot sc anz
  "$logic_and" -> do
    w <- outputWidth
    ta <- input "A"
    tb <- input "B"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    bnz <- liftIO $ SC.scBvNonzero sc w tb
    liftIO $ SC.scAnd sc anz bnz
  "$logic_or" -> do
    w <- outputWidth
    ta <- input "A"
    tb <- input "B"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    bnz <- liftIO $ SC.scBvNonzero sc w tb
    liftIO $ SC.scOr sc anz bnz
  -- "$mux" -> _
  -- "$pmux" -> _
  -- "$bmux" -> _
  -- "$demux" -> _
  -- "$lut" -> _
  -- "$slice" -> _
  -- "$concat" -> _
  (flip Map.lookup env -> Just term) -> do
    r <- cryptolRecord sc args
    liftIO $ SC.scApply sc term r
  ct -> throw . YosysError $ "Unknown cell type: " <> ct
  where
    nm = c ^. cellType
    outputWidth :: m SC.Term
    outputWidth =
      liftIO $ SC.scNat sc $ case Map.lookup "Y" $ c ^. cellConnections of
        Nothing -> panic "cellToTerm" [Text.unpack $ mconcat ["Missing expected output name for ", nm, " cell"]]
        Just bits -> fromIntegral $ length bits
    input :: Text -> m SC.Term
    input inpNm =
      case Map.lookup inpNm args of
        Nothing -> panic "cellToTerm" [Text.unpack $ mconcat [nm, " missing input ", inpNm]]
        Just a -> pure a
    bvUnaryOp :: (SC.Term -> SC.Term -> IO SC.Term) -> m SC.Term
    bvUnaryOp f = do
      t <- input "A"
      w <- outputWidth
      res <- liftIO $ f w t
      cryptolRecord sc $ Map.fromList
        [ ("Y", res)
        ]
    bvBinaryOp :: (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> m SC.Term
    bvBinaryOp f = do
      ta <- input "A"
      tb <- input "B"
      w <- outputWidth
      res <- liftIO $ f w ta tb
      cryptolRecord sc $ Map.fromList
        [ ("Y", res)
        ]
    bvNAryOp :: (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> m SC.Term
    bvNAryOp f =
      case Foldable.toList args of
        [] -> panic "cellToTerm" [Text.unpack $ mconcat [nm, " cell given no inputs"]]
        (t:rest) -> do
          w <- outputWidth
          res <- liftIO $ foldM (f w) t rest
          cryptolRecord sc $ Map.fromList
            [ ("Y", res)
            ]
    bvReduce :: Bool -> SC.Term -> m SC.Term
    bvReduce boolIdentity boolFun = do
      t <- input "A"
      w <- outputWidth
      boolTy <- liftIO $ SC.scBoolType sc
      identity <- liftIO $ SC.scBool sc boolIdentity
      scFoldr <- liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "foldr"
      res <- liftIO $ SC.scApplyAll sc scFoldr [boolTy, boolTy, w, boolFun, identity, t]
      cryptolRecord sc $ Map.fromList
        [ ("Y", res)
        ]

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
  m (SC.Term, SC.Term, C.Type)
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
  outputRecordType <- cryptolRecordType sc . Map.fromList =<< forM outputports
    (\(nm, out) -> do
        tp <- liftIO . SC.scBitvector sc . fromIntegral $ length out
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
  ty <- liftIO $ SC.scFun sc inputRecordType outputRecordType
  let toCryptol (nm, rep) = (C.mkIdent nm, C.tWord . C.tNum $ length rep)
  let cty = C.tFun
        (C.tRec . C.recordFromFields $ toCryptol <$> inputports)
        (C.tRec . C.recordFromFields $ toCryptol <$> outputports)
  pure (t, ty, cty)

-- | Given a Yosys IR and the name of a VHDL module, construct a SAWCore term for that module.
yosysIRToRecordTerm ::
  MonadIO m =>
  SC.SharedContext ->
  YosysIR ->
  m SC.TypedTerm
yosysIRToRecordTerm sc ir = do
  let mg = yosysIRModgraph ir
  let sorted = Graph.reverseTopSort $ mg ^. modgraphGraph
  (termEnv, typeEnv) <- foldM
    (\(termEnv, typeEnv) v -> do
        let (m, nm, _) = mg ^. modgraphNodeFromVertex $ v
        (t, ty, cty) <- moduleToTerm sc termEnv m
        let uri = URI.URI
              { URI.uriScheme = URI.mkScheme "yosys"
              , URI.uriAuthority = Left True
              , URI.uriPath = (False,) <$> mapM URI.mkPathPiece (nm NE.:| [])
              , URI.uriQuery = []
              , URI.uriFragment = Nothing
              }
        let ni = SC.ImportedName uri [nm]
        tc <- liftIO $ SC.scConstant' sc ni t ty
        pure
          ( Map.insert nm tc termEnv
          , Map.insert nm cty typeEnv
          )
    )
    (Map.empty, Map.empty)
    sorted
  record <- cryptolRecord sc termEnv
  let cty = C.tRec . C.recordFromFields $ first C.mkIdent <$> Map.assocs typeEnv
  let tt = SC.TypedTerm (SC.TypedTermSchema $ C.tMono cty) record
  pure tt

--------------------------------------------------------------------------------
-- ** Functions visible from SAWScript REPL

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

yosys_import :: FilePath -> TopLevel SC.TypedTerm
yosys_import path = do
  sc <- getSharedContext
  ir <- loadYosysIR path
  yosysIRToRecordTerm sc ir