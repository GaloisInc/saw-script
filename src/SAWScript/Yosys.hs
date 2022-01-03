{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language LambdaCase #-}
{-# Language TupleSections #-}

module SAWScript.Yosys
  ( YosysIR
  , yosys_load_module
  , yosys_extract
  ) where

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

import qualified Cryptol.TypeCheck.Type as Cryptol

import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedTerm as SC

import SAWScript.Panic (panic)
import SAWScript.Value
import SAWScript.Yosys.IR

--------------------------------------------------------------------------------
-- ** Building a network graph from Yosys IR

data Netgraph = Netgraph
  { _netgraphGraph :: Graph.Graph
  , _netgraphNodeFromVertex :: Graph.Vertex -> (Cell, [Bitrep], [[Bitrep]])
  , _netgraphVertexFromKey :: [Bitrep] -> Maybe Graph.Vertex
  }
makeLenses ''Netgraph

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

-- | Given a Yosys cell and terms for its arguments, construct a term representing the output.
cellToTerm :: MonadIO m => SC.SharedContext -> Cell -> [SC.Term] -> m SC.Term
cellToTerm sc c args = case c ^. cellType of
  -- TODO better handling here. consider multiple-output cells?
  CellTypeOr -> do
    w <- liftIO $ SC.scNat sc $ case Map.lookup "Y" $ c ^. cellConnections of
      Nothing -> panic "cellToTerm" ["Missing expected output name for $or cell"]
      Just bits -> fromIntegral $ length bits
    identity <- liftIO $ SC.scBvBool sc w =<< SC.scBool sc False
    liftIO $ foldM (SC.scBvOr sc w) identity args
  CellTypeAnd -> do
    w <- liftIO $ SC.scNat sc $ case Map.lookup "Y" $ c ^. cellConnections of
      Nothing -> panic "cellToTerm" ["Missing expected output name for $and cell"]
      Just bits -> fromIntegral $ length bits
    identity <- liftIO $ SC.scBvBool sc w =<< SC.scBool sc True
    liftIO $ foldM (SC.scBvAnd sc w) identity args

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
netgraphToTerms :: MonadIO m => SC.SharedContext -> Netgraph -> Map [Bitrep] SC.Term -> m (Map [Bitrep] SC.Term)
netgraphToTerms sc ng inputs
  | length (Graph.scc $ ng ^. netgraphGraph ) > 1
  = throw $ YosysError "Network graph contains a cycle; SAW does not currently support analysis of sequential circuits."
  | otherwise = do
      let sorted = Graph.reverseTopSort $ ng ^. netgraphGraph
      foldM
        ( \acc v -> do
            let (c, out, inp) = ng ^. netgraphNodeFromVertex $ v
            args <- forM inp $ \i -> -- for each input bit pattern
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
            t <- cellToTerm sc c args -- once we've built a term, insert it along with each of its bits
            derived <- deriveTermsByIndices sc out t
            pure $ Map.union derived acc
        )
        inputs
        sorted

-- | Given a Yosys IR, the name of a VHDL module, and the name of an output port, construct a
-- SAWCore term for the value of that output port.
yosysIRToTerm :: MonadIO m => SC.SharedContext -> YosysIR -> Text -> Text -> m SC.TypedTerm
yosysIRToTerm sc ir modnm portnm = do
  m <- case Map.lookup modnm $ ir ^. yosysModules of
    Just m -> pure m
    Nothing -> throw . YosysError $ "Failed to find module: " <> modnm --
  p <- case Map.lookup portnm $ m ^. modulePorts of
    Just p
      | p ^. portDirection == DirectionOutput
        || p ^. portDirection == DirectionInout
        -> pure p
      | otherwise -> throw . YosysError $ mconcat ["Port ", portnm, " is not an output port"]
    Nothing -> throw . YosysError $ "Failed to find port: " <> portnm
  let ng = moduleNetgraph m
  let inputports = Maybe.mapMaybe
        ( \(nm, ip) ->
            if ip ^. portDirection == DirectionInput || ip ^. portDirection == DirectionInout
            then Just (nm, ip ^. portBits)
            else Nothing
        )
        . Map.assocs
        $ m ^. modulePorts
  (derivedInputs, extCns) <- fmap unzip . forM inputports $ \(nm, inp) -> do
    tp <- liftIO . SC.scBitvector sc . fromIntegral $ length inp
    ec <- liftIO $ SC.scFreshEC sc nm tp
    t <- liftIO $ SC.scExtCns sc ec
    derived <- deriveTermsByIndices sc inp t
    pure (derived, ec)
  let inputs = foldr Map.union Map.empty derivedInputs
  env <- netgraphToTerms sc ng inputs
  case Map.lookup (p ^. portBits) env of
    Just unwrapped -> do
      t <- liftIO $ SC.scAbstractExts sc extCns unwrapped
      liftIO $ SC.mkTypedTerm sc t
    Nothing -> throw . YosysError $ "Failed to find output for bits: " <> (Text.pack . show $ p ^. portBits)

--------------------------------------------------------------------------------
-- ** Functions visible from SAWScript REPL

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

yosys_load_module :: FilePath -> TopLevel YosysIR
yosys_load_module = loadYosysIR

yosys_extract :: YosysIR -> String -> String -> TopLevel SC.TypedTerm
yosys_extract ir modnm portnm = do
  sc <- getSharedContext
  yosysIRToTerm sc ir (Text.pack modnm) (Text.pack portnm)
