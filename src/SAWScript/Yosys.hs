{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language ViewPatterns #-}
{-# Language LambdaCase #-}
{-# Language MultiWayIf #-}
{-# Language TupleSections #-}
{-# Language ScopedTypeVariables #-}

module SAWScript.Yosys
  ( YosysIR
  , yosys_import
  , yosys_verify
  , loadYosysIR
  , yosysIRToTypedTerms
  ) where

import Control.Lens.TH (makeLenses)

import Control.Lens (at, view, (^.))
import Control.Monad (forM, foldM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Exception (throw)

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

import Numeric.Natural (Natural)

import qualified Text.URI as URI

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedTerm as SC
import qualified Verifier.SAW.Name as SC

import qualified Cryptol.TypeCheck.Type as C
import qualified Cryptol.Utils.Ident as C
import qualified Cryptol.Utils.RecordMap as C

import SAWScript.Panic (panic)
import SAWScript.Value
import qualified SAWScript.Builtins as Builtins

import SAWScript.Yosys.IR
import SAWScript.Yosys.Theorem

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
  , _netgraphNodeFromVertex :: Graph.Vertex -> ((Text, Cell), Bitrep, [Bitrep])
  -- , _netgraphVertexFromKey :: Bitrep -> Maybe Graph.Vertex
  }
makeLenses ''Netgraph

cellInputConnections :: Cell -> Map Text [Bitrep]
cellInputConnections c
  | c ^. cellType == "$dff" = Map.empty
  | otherwise = Map.intersection (c ^. cellConnections) inp
  where
    inp = Map.filter (\d -> d == DirectionInput || d == DirectionInout) $ c ^. cellPortDirections

cellOutputConnections :: Cell -> Map [Bitrep] Text
cellOutputConnections c = Map.fromList . fmap Tuple.swap . Map.toList $ Map.intersection (c ^. cellConnections) out
  where
    out = Map.filter (\d -> d == DirectionOutput || d == DirectionInout) $ c ^. cellPortDirections

moduleNetgraph :: Module -> Netgraph
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
      $ m ^. modulePorts
    cellToNodes :: (Text, Cell) -> [((Text, Cell), Bitrep, [Bitrep])]
    cellToNodes (nm, c)
      | c ^. cellType == "$dff" = ((nm, c), , []) <$> outputBits
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
  , _convertedModuleStateFields :: Maybe (Map Text (SC.Term, C.Type))
  }
makeLenses ''ConvertedModule

-- | Given a Yosys cell and a map of terms for its arguments, construct a term representing the output.
cellToTerm ::
  forall m a.
  MonadIO m =>
  SC.SharedContext ->
  Map Text ConvertedModule {- ^ Environment of user-defined cells -} ->
  Map Text a {- ^ Mapping from output names used to construct record lookups -} ->
  Maybe SC.Term {- ^ State term for this cell, if it exists -} ->
  Cell {- ^ Cell type -} ->
  Map Text SC.Term {- ^ Mapping of input names to input terms -} ->
  m (SC.Term, Maybe SC.Term)
cellToTerm sc env outputFields mst c args = case c ^. cellType of
  "$dff"
    | Just st <- mst -> do
        fmap (,Nothing) . cryptolRecord sc $ Map.fromList
          [ ("Q", st)
          ]
    | otherwise -> panic "cellToTerm" [Text.unpack $ mconcat ["Flip-flop cell has no associated state term"]]
  "$not" -> bvUnaryOp $ SC.scBvNot sc
  "$pos" -> do
    res <- input "A"
    fmap (,Nothing) . cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
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
  "$lt" -> bvBinaryCmp $ SC.scBvULt sc
  "$le" -> bvBinaryCmp $ SC.scBvULe sc
  "$gt" -> bvBinaryCmp $ SC.scBvUGt sc
  "$ge" -> bvBinaryCmp $ SC.scBvUGe sc
  "$eq" -> bvBinaryCmp $ SC.scBvEq sc
  "$ne" -> bvBinaryCmp $ \w x y -> do
    r <- SC.scBvEq sc w x y
    SC.scNot sc r
  "$eqx" -> bvBinaryCmp $ SC.scBvEq sc
  "$nex" -> bvBinaryCmp $ \w x y -> do
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
    res <- liftIO $ SC.scNot sc anz
    fmap (,Nothing) . cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  "$logic_and" -> do
    w <- outputWidth
    ta <- input "A"
    tb <- input "B"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    bnz <- liftIO $ SC.scBvNonzero sc w tb
    res <- liftIO $ SC.scAnd sc anz bnz
    fmap (,Nothing) . cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  "$logic_or" -> do
    w <- outputWidth
    ta <- input "A"
    tb <- input "B"
    anz <- liftIO $ SC.scBvNonzero sc w ta
    bnz <- liftIO $ SC.scBvNonzero sc w tb
    res <- liftIO $ SC.scOr sc anz bnz
    fmap (,Nothing) . cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  "$mux" -> do
    w <- outputWidth
    ta <- input "A"
    tb <- input "B"
    ts <- input "S"
    snz <- liftIO $ SC.scBvNonzero sc w ts
    ty <- liftIO $ SC.scBitvector sc outputWidthNat
    res <- liftIO $ SC.scIte sc ty snz tb ta
    fmap (,Nothing) . cryptolRecord sc $ Map.fromList
      [ ("Y", res)
      ]
  -- "$pmux" -> _
  -- "$bmux" -> _
  -- "$demux" -> _
  -- "$lut" -> _
  -- "$slice" -> _
  -- "$concat" -> _
  (flip Map.lookup env -> Just cm) -> do
    r <- cryptolRecord sc $ case mst of
      Nothing -> args
      Just st -> Map.insert "__state__" st args
    res <- liftIO $ SC.scApply sc (cm ^. convertedModuleTerm) r
    post <- case mst of
      Nothing -> pure Nothing
      Just _ -> Just <$> cryptolRecordSelect sc outputFields res "__state__"
    pure (res, post)
  ct -> throw . YosysError $ "Unknown cell type: " <> ct
  where
    nm = c ^. cellType
    outputWidthNat :: Natural
    outputWidthNat =
      case Map.lookup "Y" $ c ^. cellConnections of
        Nothing -> panic "cellToTerm" [Text.unpack $ mconcat ["Missing expected output name for ", nm, " cell"]]
        Just bits -> fromIntegral $ length bits
    outputWidth :: m SC.Term
    outputWidth = liftIO $ SC.scNat sc outputWidthNat
    input :: Text -> m SC.Term
    input inpNm =
      case Map.lookup inpNm args of
        Nothing -> panic "cellToTerm" [Text.unpack $ mconcat [nm, " missing input ", inpNm]]
        Just a -> pure a
    bvUnaryOp :: (SC.Term -> SC.Term -> IO SC.Term) -> m (SC.Term, Maybe SC.Term)
    bvUnaryOp f = do
      t <- input "A"
      w <- outputWidth
      res <- liftIO $ f w t
      fmap (,Nothing) . cryptolRecord sc $ Map.fromList
        [ ("Y", res)
        ]
    bvBinaryOp :: (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> m (SC.Term, Maybe SC.Term)
    bvBinaryOp f = do
      ta <- input "A"
      tb <- input "B"
      w <- outputWidth
      res <- liftIO $ f w ta tb
      fmap (,Nothing) . cryptolRecord sc $ Map.fromList
        [ ("Y", res)
        ]
    bvBinaryCmp :: (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> m (SC.Term, Maybe SC.Term)
    bvBinaryCmp f = do
      ta <- input "A"
      tb <- input "B"
      w <- outputWidth
      bit <- liftIO $ f w ta tb
      boolty <- liftIO $ SC.scBoolType sc
      res <- liftIO $ SC.scSingle sc boolty bit
      fmap (,Nothing) . cryptolRecord sc $ Map.fromList
        [ ("Y", res)
        ]
    bvNAryOp :: (SC.Term -> SC.Term -> SC.Term -> IO SC.Term) -> m (SC.Term, Maybe SC.Term)
    bvNAryOp f =
      case Foldable.toList args of
        [] -> panic "cellToTerm" [Text.unpack $ mconcat [nm, " cell given no inputs"]]
        (t:rest) -> do
          w <- outputWidth
          res <- liftIO $ foldM (f w) t rest
          fmap (,Nothing) . cryptolRecord sc $ Map.fromList
            [ ("Y", res)
            ]
    bvReduce :: Bool -> SC.Term -> m (SC.Term, Maybe SC.Term)
    bvReduce boolIdentity boolFun = do
      t <- input "A"
      w <- outputWidth
      boolTy <- liftIO $ SC.scBoolType sc
      identity <- liftIO $ SC.scBool sc boolIdentity
      scFoldr <- liftIO . SC.scLookupDef sc $ SC.mkIdent SC.preludeName "foldr"
      bit <- liftIO $ SC.scApplyAll sc scFoldr [boolTy, boolTy, w, boolFun, identity, t]
      boolty <- liftIO $ SC.scBoolType sc
      res <- liftIO $ SC.scSingle sc boolty bit
      fmap (,Nothing) . cryptolRecord sc $ Map.fromList
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

lookupPatternTerm ::
  MonadIO m =>
  SC.SharedContext ->
  [Bitrep] ->
  Map [Bitrep] SC.Term ->
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
  MonadIO m =>
  SC.SharedContext ->
  Map Text ConvertedModule ->
  Map Text (SC.Term, C.Type) ->
  Maybe SC.Term ->
  Netgraph ->
  Map [Bitrep] SC.Term ->
  m (Map [Bitrep] SC.Term, Map Text SC.Term)
netgraphToTerms sc env stateFields mst ng inputs
  | length (Graph.scc $ ng ^. netgraphGraph) /= length (ng ^. netgraphGraph)
  = do
      throw $ YosysError "Network graph contains a cycle after splitting on DFFs; SAW does not currently support analysis of this circuit"
  | otherwise = do
      let sorted = Graph.reverseTopSort $ ng ^. netgraphGraph
      foldM
        ( \(acc, stateAcc) v -> do
            let ((nm, c), _output, _deps) = ng ^. netgraphNodeFromVertex $ v
            -- liftIO $ putStrLn $ mconcat ["Building term for output: ", show output, " and inputs: ", show deps]

            args <- forM (cellInputConnections c) $ \i -> do -- for each input bit pattern
              -- if we can find that pattern exactly, great! use that term
              -- otherwise, find each individual bit and append the terms
              lookupPatternTerm sc i acc

            let portFields = Map.filter (\d -> d == DirectionOutput || d == DirectionInout) $ c ^. cellPortDirections
            (cellmst, outputFields) <- case mst of
              Just st
                | Just _ <- Map.lookup nm stateFields -> do
                    cellmst <- Just <$> cryptolRecordSelect sc stateFields st nm
                    pure (cellmst, if c ^. cellType == "$dff" then portFields else Map.insert "__state__" DirectionOutput portFields)
              _ -> pure (Nothing, portFields)

            (r, mpost) <- cellToTerm sc env outputFields cellmst c args

            -- once we've built a term, insert it along with each of its bits
            ts <- forM (Map.assocs $ cellOutputConnections c) $ \(out, o) -> do
              t <- cryptolRecordSelect sc outputFields r o
              deriveTermsByIndices sc out t
            pure
              ( Map.union (Map.unions ts) acc
              , case mpost of
                  Nothing -> stateAcc
                  Just post -> Map.insert nm post stateAcc
              )
        )
        (inputs, Map.empty)
        sorted

convertModule ::
  MonadIO m =>
  SC.SharedContext ->
  Map Text ConvertedModule ->
  Module ->
  m ConvertedModule
convertModule sc env m = do
  let ng = moduleNetgraph m
  let clockCandidates = List.nub
        . Maybe.mapMaybe
        ( \(_nm, c) -> if c ^. cellType == "$dff"
          then Map.lookup "CLK" (c ^. cellConnections)
          else Nothing
        )
        . Map.assocs
        $ m ^. moduleCells
  let clockBits = case clockCandidates of
        [] -> []
        [b] -> b
        _ -> throw . YosysError $ mconcat
          [ "Multiple clocks detected (bits: "
          , Text.pack $ show clockCandidates
          , ")\nSAW only supports sequential circuits with a single clock"
          ]

  let inputports = Maybe.mapMaybe
        ( \(nm, ip) ->
            if
              (ip ^. portDirection == DirectionInput || ip ^. portDirection == DirectionInout)
              && (ip ^. portBits /= clockBits)
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

  stateFields <- Map.fromList
        . Maybe.catMaybes
        <$> mapM
        ( \v ->
            let ((nm, c), _output, _deps) = ng ^. netgraphNodeFromVertex $ v
            in if
              | c ^. cellType == "$dff"
              , Just b <- Map.lookup "Q" $ c ^. cellConnections -> do
                  let w = length b
                  ty <- liftIO $ SC.scBitvector sc $ fromIntegral w
                  let cty = C.tWord $ C.tNum w
                  pure $ Just (nm, (ty, cty))
              | Just cm <- Map.lookup (c ^. cellType) env
              , Just fields <- cm ^. convertedModuleStateFields -> do
                  ty <- cryptolRecordType sc (fst <$> fields)
                  let cty = C.tRec . C.recordFromFields $ (\(cnm, (_, t)) -> (C.mkIdent cnm, t)) <$> Map.assocs fields
                  pure $ Just (nm, (ty, cty))
              | otherwise -> pure Nothing
        )
        (Graph.vertices $ ng ^. netgraphGraph)
  stateRecordType <- cryptolRecordType sc $ fst <$> stateFields
  let stateRecordCryptolType = C.tRec . C.recordFromFields $ (\(cnm, (_, t)) -> (C.mkIdent cnm, t)) <$> Map.assocs stateFields

  let addStateType fs = if Map.null stateFields then fs else Map.insert "__state__" stateRecordType fs
  inputFields <- addStateType . Map.fromList <$> forM inputports
    (\(nm, inp) -> do
        tp <- liftIO . SC.scBitvector sc . fromIntegral $ length inp
        pure (nm, tp)
    )
  outputFields <- addStateType . Map.fromList <$> forM outputports
    (\(nm, out) -> do
        tp <- liftIO . SC.scBitvector sc . fromIntegral $ length out
        pure (nm, tp)
    )
  inputRecordType <- cryptolRecordType sc inputFields
  outputRecordType <- cryptolRecordType sc outputFields
  inputRecordEC <- liftIO $ SC.scFreshEC sc "input" inputRecordType
  inputRecord <- liftIO $ SC.scExtCns sc inputRecordEC

  derivedInputs <- forM inputports $ \(nm, inp) -> do
    t <- liftIO $ cryptolRecordSelect sc inputFields inputRecord nm
    deriveTermsByIndices sc inp t

  stateRecordTerm <- if Map.null stateFields
    then pure Nothing
    else liftIO $ Just <$> cryptolRecordSelect sc inputFields inputRecord "__state__"

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

  (terms, modulePostStates) <- netgraphToTerms sc env stateFields stateRecordTerm ng inputs
  dffBackedges <- fmap (Map.fromList . Maybe.catMaybes)
        . mapM
        ( \(nm, c) -> if
            | c ^. cellType == "$dff"
            , Just b <- Map.lookup "D" (c ^. cellConnections)
            -> do
                t <- lookupPatternTerm sc b terms
                pure $ Just (nm, t)
            | otherwise -> pure Nothing
        )
        . Map.assocs
        $ m ^. moduleCells
  let postStateFields = Map.union dffBackedges modulePostStates
  postStateRecord <- cryptolRecord sc postStateFields

  let addState fs = if Map.null stateFields then fs else Map.insert "__state__" postStateRecord fs
  outputRecord <- cryptolRecord sc . addState . Map.fromList =<< forM outputports
    (\(nm, out) -> (nm,) <$> lookupPatternTerm sc out terms)

  t <- liftIO $ SC.scAbstractExts sc [inputRecordEC] outputRecord
  ty <- liftIO $ SC.scFun sc inputRecordType outputRecordType

  let addStateCryptolType fs = if Map.null stateFields then fs else ("__state__", stateRecordCryptolType):fs
  let toCryptol (nm, rep) = (C.mkIdent nm, C.tWord . C.tNum $ length rep)
  let cty = C.tFun
        (C.tRec . C.recordFromFields . addStateCryptolType $ toCryptol <$> inputports)
        (C.tRec . C.recordFromFields . addStateCryptolType $ toCryptol <$> outputports)
  pure ConvertedModule
    { _convertedModuleTerm = t
    , _convertedModuleType = ty
    , _convertedModuleCryptolType = cty
    , _convertedModuleStateFields = if Map.null stateFields then Nothing else Just stateFields
    }

-- | Given a Yosys IR, construct records associating module names with SAWCore terms and Cryptol types.
yosysIRToTerms ::
  MonadIO m =>
  SC.SharedContext ->
  YosysIR ->
  m (Map Text ConvertedModule)
yosysIRToTerms sc ir = do
  let mg = yosysIRModgraph ir
  let sorted = Graph.reverseTopSort $ mg ^. modgraphGraph
  foldM
    (\env v -> do
        let (m, nm, _) = mg ^. modgraphNodeFromVertex $ v
        -- liftIO . putStrLn . Text.unpack $ mconcat ["Converting module: ", nm]
        cm <- convertModule sc env m
        let uri = URI.URI
              { URI.uriScheme = URI.mkScheme "yosys"
              , URI.uriAuthority = Left True
              , URI.uriPath = (False,) <$> mapM URI.mkPathPiece (nm NE.:| [])
              , URI.uriQuery = []
              , URI.uriFragment = Nothing
              }
        let ni = SC.ImportedName uri [nm]
        tc <- liftIO $ SC.scConstant' sc ni (cm ^. convertedModuleTerm) (cm ^. convertedModuleType)
        let cm' = cm { _convertedModuleTerm = tc }
        pure $ Map.insert nm cm' env
    )
    Map.empty
    sorted

-- | Given a Yosys IR, construct a record of TypedTerms
yosysIRToTypedTerms ::
  MonadIO m =>
  SC.SharedContext ->
  YosysIR ->
  m (Map Text SC.TypedTerm)
yosysIRToTypedTerms sc ir = do
  env <- yosysIRToTerms sc ir
  res <- forM (Map.assocs env) $ \(nm, cm) ->
    pure
    ( nm
    , SC.TypedTerm
      (SC.TypedTermSchema $ C.tMono $ cm ^. convertedModuleCryptolType)
      $ cm ^. convertedModuleTerm
    )
  pure $ Map.fromList res

-- | Given a Yosys IR, construct a SAWCore record for all modules.
yosysIRToRecordTerm ::
  MonadIO m =>
  SC.SharedContext ->
  YosysIR ->
  m SC.TypedTerm
yosysIRToRecordTerm sc ir = do
  env <- yosysIRToTerms sc ir
  record <- cryptolRecord sc $ view convertedModuleTerm <$> env
  let cty = C.tRec . C.recordFromFields $ (\(nm, cm) -> (C.mkIdent nm, cm ^. convertedModuleCryptolType)) <$> Map.assocs env
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

yosys_verify :: SC.TypedTerm -> [SC.TypedTerm] -> SC.TypedTerm -> [YosysTheorem] -> ProofScript () -> TopLevel YosysTheorem
yosys_verify ymod preconds other specs tactic = do
  sc <- getSharedContext
  newmod <- foldM (flip $ applyOverride sc)
    (SC.ttTerm ymod)
    specs
  mpc <- case preconds of
    [] -> pure Nothing
    (pc:pcs) -> do
      t <- foldM (\a b -> liftIO $ SC.scAnd sc a b) (SC.ttTerm pc) (SC.ttTerm <$> pcs)
      pure . Just $ SC.TypedTerm (SC.ttType pc) t
  thm <- buildTheorem sc ymod newmod mpc other
  prop <- theoremProp sc thm
  _ <- Builtins.provePrintPrim tactic prop
  pure thm
