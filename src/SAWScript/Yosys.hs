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

cellToTerm :: MonadIO m => SC.SharedContext -> Cell -> [SC.Term] -> m SC.Term
cellToTerm sc c args = case c ^. cellType of
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

netgraphToTerms :: MonadIO m => SC.SharedContext -> Netgraph -> Map [Bitrep] SC.Term -> m (Map [Bitrep] SC.Term)
netgraphToTerms sc ng inputs = do
  let sorted = Graph.reverseTopSort $ ng ^. netgraphGraph
  foldM
    ( \acc v -> do
        let (c, out, inp) = ng ^. netgraphNodeFromVertex $ v
        args <- forM inp $ \i ->
          -- TODO: be smarter on this lookup! may want to insert terms for individual bits.
          case Map.lookup i acc of
            Just t -> pure t
            Nothing -> throw . YosysError $ "Failed to find output bitvec: " <> Text.pack (show i)
        t <- cellToTerm sc c args
        pure $ Map.insert out t acc
    )
    inputs
    sorted

--------------------------------------------------------------------------------
-- ** Building a SAWCore term from a network graph

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
  inputs <- fmap Map.fromList . forM inputports $ \(nm, inp) -> do
    tp <- liftIO . SC.scBitvector sc . fromIntegral $ length inp
    ec <- liftIO $ SC.scFreshEC sc nm tp
    t <- liftIO $ SC.scExtCns sc ec
    pure (inp, t)
  env <- netgraphToTerms sc ng inputs
  case Map.lookup (p ^. portBits) env of
    Just t -> do
      let cty = Cryptol.tWord (Cryptol.tNum . length $ p ^. portBits)
      pure $ SC.TypedTerm (SC.TypedTermSchema (Cryptol.tMono cty)) t
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
