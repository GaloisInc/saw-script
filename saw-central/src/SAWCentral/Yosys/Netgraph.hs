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

import qualified Data.Aeson as Aeson
import qualified Data.Maybe as Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
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

-- | A 'Netgraph' represents the data dependencies between 'Cell's in
-- a module. The graph has 'Text' keys which are the cell instance
-- names.
data Netgraph = Netgraph
  { _netgraphGraph :: Graph.Graph
  , _netgraphNodeFromVertex :: Graph.Vertex -> (Cell [Bitrep], CellInstName, [CellInstName])
  -- , _netgraphVertexFromKey :: Text -> Maybe Graph.Vertex
  }
makeLenses ''Netgraph

moduleNetgraph :: Module -> Netgraph
moduleNetgraph m =
  let
    sources :: Map Bitrep CellInstName
    sources =
      Map.fromList $
      [ (b, cname)
      | (cname, c) <- Map.assocs (m ^. moduleCells)
      , b <- concat (Map.elems (cellOutputConnections c)) ]

    cellDeps :: Cell [Bitrep] -> [CellInstName]
    cellDeps c
      | cellIsRegister c = []
      | otherwise =
        Set.toAscList $ Set.fromList $
        Maybe.mapMaybe (flip Map.lookup sources) $
        concat $ Map.elems $ cellInputConnections c

    nodes :: [(Cell [Bitrep], CellInstName, [CellInstName])]
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
  (Ord b, Show b) =>
  SC.SharedContext ->
  YosysBitvecConsumer ->
  [b] ->
  Map [b] Preterm ->
  IO SC.Term
lookupPatternTerm sc loc pat ts =
  case Map.lookup pat ts of
    -- if we can find that pattern exactly, great! use that term
    Just t -> scPreterm sc t
    -- otherwise, find each individual bit and append the terms
    Nothing ->
      do bits <-
           forM pat $ \b ->
           case Map.lookup [b] ts of
             Just t -> pure t
             Nothing -> yosysError $ YosysErrorNoSuchOutputBitvec (Text.pack $ show b) loc
         -- Yosys lists bits in little-endian order, while scVector expects big-endian, so reverse
         let ps = fusePreterms (reverse bits)
         scPreterms sc ps

-- | Given a netgraph and an initial map from bit patterns to terms, populate that map with terms
-- generated from the rest of the netgraph.
netgraphToTerms ::
  SC.SharedContext ->
  Map CellTypeName ConvertedModule ->
  Netgraph ->
  Map [Bitrep] Preterm ->
  IO (Map [Bitrep] Preterm)
netgraphToTerms sc env ng inputs
  | length (Graph.scc $ ng ^. netgraphGraph) /= length (ng ^. netgraphGraph)
  = yosysError $ YosysError "Network graph contains a cycle after splitting on DFFs; SAW does not currently support analysis of this circuit"
  | otherwise =
      let sorted = reverseTopSort $ ng ^. netgraphGraph
      in foldM doVertex inputs sorted
  where
    doVertex :: Map [Bitrep] Preterm -> Graph.Vertex -> IO (Map [Bitrep] Preterm)
    doVertex acc v =
      do let (c, cnm, _deps) = ng ^. netgraphNodeFromVertex $ v
         let outputFields = Map.filter isOutput (c ^. cellPortDirections)
         let lookupConn portname =
               case Map.lookup portname (c ^. cellConnections) of
                 Nothing ->
                   yosysError $
                   YosysError $
                   "Malformed Yosys file: Missing port " <> portname <> " for cell " <> cnm
                 Just bs ->
                   pure bs

         case c ^. cellType of
           CellTypeCombinational ctc ->
             do let doInput inm i =
                      do t <- lookupPatternTerm sc (YosysBitvecConsumerCell cnm inm) i acc
                         let w = fromIntegral (length i)
                         let s =
                               case Map.lookup (inm <> "_SIGNED") (c ^. cellParameters) of
                                 Just (Aeson.Number n) -> n > 0
                                 Just (Aeson.String x) -> textBinNat x > 0
                                 Just _ -> False
                                 Nothing -> False
                         pure (CellTerm t w s)
                args <- Map.traverseWithKey doInput (cellInputConnections c)
                bs <- lookupConn "Y"
                let ywidth = fromIntegral (length bs)
                t <- combCellToTerm sc ctc args ywidth
                ts <- deriveTermsByIndices sc bs t
                pure $ Map.union ts acc
           -- special handling for $dff/$ff nodes - we read their
           -- /output/ from the inputs map, and later detect and write
           -- their /input/ to the state
           CellTypeDff ->
             do dffout <- lookupConn "Q"
                r <- lookupPatternTerm sc (YosysBitvecConsumerCell cnm "Q") dffout acc
                ts <- deriveTermsByIndices sc dffout r
                pure $ Map.union ts acc
           CellTypeFf ->
             do ffout <- lookupConn "Q"
                r <- lookupPatternTerm sc (YosysBitvecConsumerCell cnm "Q") ffout acc
                ts <- deriveTermsByIndices sc ffout r
                pure $ Map.union ts acc
           CellTypeUnsupportedPrimitive nm
             | Map.null outputFields ->
                 -- Cells with no output ports are debugging cells, which we can simply ignore.
                 pure acc
             | otherwise ->
                 yosysError $ YosysErrorUnsupportedFF nm
           CellTypeUserType submoduleName ->
             case Map.lookup submoduleName env of
               Nothing ->
                 yosysError $ YosysErrorNoSuchSubmodule submoduleName cnm
               Just cm ->
                 do let doInput inm i = lookupPatternTerm sc (YosysBitvecConsumerCell cnm inm) i acc
                    args <- Map.traverseWithKey doInput (cellInputConnections c)
                    rin <- cryptolRecord sc args
                    r <- SC.scApply sc (cm ^. convertedModuleTerm) rin
                    -- once we've built a term, insert it along with each of its bits
                    ts <-
                      forM (Map.assocs $ cellOutputConnections c) $ \(o, out) ->
                      do t <- cryptolRecordSelect sc outputFields r o
                         deriveTermsByIndices sc out t
                    pure $ Map.union (Map.unions ts) acc

convertModule ::
  SC.SharedContext ->
  Map CellTypeName ConvertedModule ->
  Module ->
  IO ConvertedModule
convertModule sc env m =
  do let ng = moduleNetgraph m

     let inputPorts = moduleInputPorts m
     let outputPorts = moduleOutputPorts m

     inputFields <- forM inputPorts
       (\inp ->
           SC.scBitvector sc . fromIntegral $ length inp
       )
     outputFields <- forM outputPorts
       (\out ->
           SC.scBitvector sc . fromIntegral $ length out
       )
     inputRecordType <- cryptolRecordType sc inputFields
     outputRecordType <- cryptolRecordType sc outputFields
     inputRecord <- SC.scFreshVariable sc "input" inputRecordType

     derivedInputs <-
       forM (Map.assocs inputPorts) $ \(nm, inp) ->
       do t <- cryptolRecordSelect sc inputFields inputRecord nm
          deriveTermsByIndices sc inp t

     oneBitType <- SC.scBitvector sc 1
     xMsg <- SC.scString sc "Attempted to read X bit"
     xTerm <- SC.scGlobalApply sc (SC.mkIdent SC.preludeName "error") [oneBitType, xMsg]
     zMsg <- SC.scString sc "Attempted to read Z bit"
     zTerm <- SC.scGlobalApply sc (SC.mkIdent SC.preludeName "error") [oneBitType, zMsg]
     let inputs = Map.unions $ mconcat
           [ [ Map.fromList
               [ ( [BitrepZero], PretermBvNat 1 0 )
               , ( [BitrepOne], PretermBvNat 1 1 )
               , ( [BitrepX], PretermSlice 0 1 0 xTerm )
               , ( [BitrepZ], PretermSlice 0 1 0 zTerm )
               ]
             ]
           , derivedInputs
           ]

     terms <- netgraphToTerms sc env ng inputs
     outputRecord <- cryptolRecord sc =<< mapForWithKeyM outputPorts
       (\onm out -> lookupPatternTerm sc (YosysBitvecConsumerOutputPort onm) out terms)

     t <- SC.scAbstractTerms sc [inputRecord] outputRecord
     ty <- SC.scFun sc inputRecordType outputRecordType

     let toCryptol (nm, rep) = (C.mkIdent nm, C.tWord . C.tNum $ length rep)
     let cty = C.tFun
           (C.tRec . C.recordFromFields $ toCryptol <$> Map.assocs inputPorts)
           (C.tRec . C.recordFromFields $ toCryptol <$> Map.assocs outputPorts)
     pure ConvertedModule
       { _convertedModuleTerm = t
       , _convertedModuleType = ty
       , _convertedModuleCryptolType = cty
       }
