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
import qualified Data.IntSet as IntSet
import qualified Data.Maybe as Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Graph as Graph

import qualified SAWCore.SharedTerm as SC
import qualified SAWCore.Name as SC

import SAWCentral.Panic (panic)

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
  -- , _netgraphVertexFromKey :: CellInstName -> Maybe Graph.Vertex
  }
makeLenses ''Netgraph

moduleNetgraph :: Map CellTypeName ConvertedModule -> Module -> Netgraph
moduleNetgraph env m =
  let
    sources :: Map Bitrep CellInstName
    sources =
      Map.fromList $
      [ (b, cname)
      | (cname, c) <- Map.assocs (m ^. moduleCells)
      , b <- concat (Map.elems (cellOutputConnections c)) ]

    isMooreMachine :: CellType -> Bool
    isMooreMachine ct =
      case ct of
        CellTypeUserType t ->
          case Map.lookup t env of
            Nothing -> False
            Just cm ->
              case _convertedModuleState cm of
                Nothing -> False
                Just (mt, _) -> mt == Moore
        _ -> False

    cellDeps :: Cell [Bitrep] -> [CellInstName]
    cellDeps c
      | cellIsRegister c = []
      | isMooreMachine (c ^. cellType) = []
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

-- | A Mealy machine allows same-cycle data flow from inputs to
-- outputs, while a Moore machine only allows the outputs to depend on
-- the internal state.
data MachineType = Mealy | Moore
  deriving Eq

-- | A SAWCore translation of a module imported from the Yosys JSON format.
data ConvertedModule = ConvertedModule
  { _convertedModuleTerm :: SC.Term
    -- ^ A SAWCore term representing the module semantics, of type
    -- @Input -> Output@ for combinational modules, @{step : Input ->
    -- State -> State, out : Input -> State -> Output}@ for Mealy
    -- machines, or @{step : Input -> State -> State, out : State ->
    -- Output}@ for Moore machines.
  , _convertedModuleState :: Maybe (MachineType, SC.Term)
    -- ^ The module's state type represented in both SAWCore and
    -- Cryptol, or 'Nothing' if the module is purely combinational.
  }
makeLenses ''ConvertedModule

-- | A mapping from wires to their corresponding terms.
type WireEnv = Map [Bitrep] Preterm

lookupPatternTerm ::
  SC.SharedContext ->
  YosysBitvecConsumer ->
  [Bitrep] ->
  WireEnv ->
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
  WireEnv ->
  Map CellInstName SC.Term {- ^ state inputs -} ->
  IO WireEnv
netgraphToTerms sc env ng inputs states
  | length (Graph.scc $ ng ^. netgraphGraph) /= length (ng ^. netgraphGraph)
  = yosysError $ YosysError "Network graph contains a cycle after splitting on DFFs; SAW does not currently support analysis of this circuit"
  | otherwise =
      let sorted = reverseTopSort $ ng ^. netgraphGraph
      in foldM doVertex inputs sorted
  where
    doVertex :: WireEnv -> Graph.Vertex -> IO WireEnv
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
           CellTypeDff ->
             do r <-
                  case Map.lookup cnm states of
                    Nothing ->
                      panic "netgraphToTerms" ["missing state for dff cell " <> cnm]
                    Just r -> pure r
                bs <- lookupConn "Q"
                ts <- deriveTermsByIndices sc bs r
                pure $ Map.union ts acc
           CellTypeFf ->
             do r <-
                  case Map.lookup cnm states of
                    Nothing -> panic "netgraphToTerms" ["missing state for ff cell " <> cnm]
                    Just r -> pure r
                bs <- lookupConn "Q"
                ts <- deriveTermsByIndices sc bs r
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
                 do inputArgs <-
                      case cm ^. convertedModuleState of
                        Just (Moore, _) -> pure []
                        _ ->
                          do let doInput inm i = lookupPatternTerm sc (YosysBitvecConsumerCell cnm inm) i acc
                             args <- Map.traverseWithKey doInput (cellInputConnections c)
                             rin <- cryptolRecord sc args
                             pure [rin]
                    let stateArgs = Maybe.maybeToList (Map.lookup cnm states)
                    f <-
                      case cm ^. convertedModuleState of
                        Nothing -> pure (cm ^. convertedModuleTerm)
                        Just _ -> SC.scRecordSelect sc (cm ^. convertedModuleTerm) "out"
                    r <- SC.scApplyAll sc f (inputArgs ++ stateArgs)

                    -- once we've built a term, insert it along with each of its bits
                    ts <-
                      forM (Map.assocs $ cellOutputConnections c) $ \(o, out) ->
                      do t <- cryptolRecordSelect sc outputFields r o
                         deriveTermsByIndices sc out t
                    pure $ Map.union (Map.unions ts) acc

-- | Compute the new state value for a stateful cell type.
cellNewState ::
  SC.SharedContext ->
  Map CellTypeName ConvertedModule ->
  WireEnv ->
  CellInstName ->
  (Cell [Bitrep], SC.Term) ->
  IO SC.Term
cellNewState sc env terms cnm (c, prevState) =
  case c ^. cellType of
    CellTypeDff ->
      do bs <- lookupConn "D"
         lookupPatternTerm sc (YosysBitvecConsumerCell cnm "D") bs terms
    CellTypeFf ->
      do bs <- lookupConn "D"
         lookupPatternTerm sc (YosysBitvecConsumerCell cnm "D") bs terms
    CellTypeCombinational _ ->
      panic "cellNewState" ["unexpected combinational cell"]
    CellTypeUnsupportedPrimitive _ ->
      panic "cellNewState" ["unexpected unsupported cell"]
    CellTypeUserType submoduleName ->
      case Map.lookup submoduleName env of
        Nothing ->
          yosysError $ YosysErrorNoSuchSubmodule submoduleName cnm
        Just cm ->
          do -- Both Mealy and Moore machines have a "step" field of type `Input -> State -> State`
             f <- SC.scRecordSelect sc (cm ^. convertedModuleTerm) "step"
             let doInput inm i = lookupPatternTerm sc (YosysBitvecConsumerCell cnm inm) i terms
             args <- Map.traverseWithKey doInput (cellInputConnections c)
             rin <- cryptolRecord sc args
             SC.scApplyAll sc f [rin, prevState]
  where
    lookupConn portname =
      case Map.lookup portname (c ^. cellConnections) of
        Nothing ->
          yosysError $
          YosysError $
          "Malformed Yosys file: Missing port " <> portname <> " for cell " <> cnm
        Just bs ->
          pure bs

convertModule ::
  SC.SharedContext ->
  Map CellTypeName ConvertedModule ->
  Module ->
  IO ConvertedModule
convertModule sc env m0 =
  do let m = renameDffInstances m0
     let ng = moduleNetgraph env m

     let inputPorts = moduleInputPorts m
     let outputPorts = moduleOutputPorts m

     let
       f :: [Bitrep] -> IO SC.Term
       f = SC.scBitvector sc . fromIntegral . length

     inputFields <- traverse f inputPorts
     inputRecordType <- cryptolRecordType sc inputFields
     inputVarName <- SC.scFreshVarName sc "input"
     inputRecord <- SC.scVariable sc inputVarName inputRecordType

     derivedInputs <-
       forM (Map.assocs inputPorts) $ \(nm, inp) ->
       do t <- cryptolRecordSelect sc inputFields inputRecord nm
          deriveTermsByIndices sc inp t

     -- Collect state types from all register cells in this module
     let
       registerCells :: Map CellInstName (Cell [Bitrep])
       registerCells = Map.filter cellIsRegister (m ^. moduleCells)
       registerPorts :: Map CellInstName [Bitrep]
       registerPorts = Map.mapMaybe (\c -> Map.lookup "Q" (c ^. cellConnections)) registerCells
     -- stateFields1 :: Map CellInstName SC.Term
     stateFields1 <- traverse f registerPorts

     -- Collect state types from all submodules
     let
       getSubmodule :: Cell [Bitrep] -> Maybe ConvertedModule
       getSubmodule c =
         case c ^. cellType of
           CellTypeUserType t -> Map.lookup t env
           _ -> Nothing
       submodules :: Map CellInstName ConvertedModule
       submodules = Map.mapMaybe getSubmodule (m ^. moduleCells)
       stateSubmodules :: Map CellInstName (MachineType, SC.Term)
       stateSubmodules = Map.mapMaybe (\cm -> cm ^. convertedModuleState) submodules
       stateFields2 :: Map CellInstName SC.Term
       stateFields2 = fmap snd stateSubmodules
       stateFields :: Map CellInstName SC.Term
       stateFields = stateFields1 <> stateFields2

     stateRecordType <- cryptolRecordType sc stateFields
     stateVarName <- SC.scFreshVarName sc "state"
     stateRecord <- SC.scVariable sc stateVarName stateRecordType
     oldstates <-
       Map.traverseWithKey (\nm _inp -> cryptolRecordSelect sc stateFields stateRecord nm) stateFields

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

     -- translate outputs of all cells in dependency order
     terms <- netgraphToTerms sc env ng inputs oldstates
     -- assemble the final output
     outputRecord <- cryptolRecord sc =<< mapForWithKeyM outputPorts
       (\onm out -> lookupPatternTerm sc (YosysBitvecConsumerOutputPort onm) out terms)

     -- translate the new state components of all stateful cells (if any)
     newstates <-
       Map.traverseWithKey (cellNewState sc env terms) $
       Map.intersectionWith (,) (m ^. moduleCells) oldstates
     newstateRecord <- cryptolRecord sc newstates

     case Map.null newstates of
       True ->
         -- No state; term for combinational module is function `Input -> Output`
         do t <- SC.scAbstractTerms sc [inputRecord] outputRecord
            pure $
              ConvertedModule
              { _convertedModuleTerm = t
              , _convertedModuleState = Nothing
              }
       False ->
         do step <- SC.scAbstractTerms sc [inputRecord, stateRecord] newstateRecord
            case IntSet.member (SC.vnIndex inputVarName) (SC.freeVars outputRecord) of
              True ->
                -- Output depends on input, so we have a Mealy machine
                do out <- SC.scAbstractTerms sc [inputRecord, stateRecord] outputRecord
                   t <- SC.scRecordValue sc [("out", out), ("step", step)]
                   pure $
                     ConvertedModule
                     { _convertedModuleTerm = t
                     , _convertedModuleState = Just (Mealy, stateRecordType)
                     }
              False ->
                -- Output does not depend on input, so we have a Moore machine
                do out <- SC.scAbstractTerms sc [stateRecord] outputRecord
                   t <- SC.scRecordValue sc [("out", out), ("step", step)]
                   pure $
                     ConvertedModule
                     { _convertedModuleTerm = t
                     , _convertedModuleState = Just (Moore, stateRecordType)
                     }
