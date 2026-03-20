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
import Control.Monad (forM, foldM, unless)
import Numeric.Natural

import qualified Data.Aeson as Aeson
import qualified Data.IntSet as IntSet
import qualified Data.Maybe as Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
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
  , _netgraphNodeFromVertex :: Graph.Vertex -> (Cell, CellInstName, [CellInstName])
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

    isMooreMachine :: CellTypeName -> Bool
    isMooreMachine t =
      case Map.lookup t env of
        Nothing -> False
        Just cm ->
          case _convertedModuleState cm of
            Nothing -> False
            Just (mt, _) -> mt == Moore

    asyncInputs :: CellTypeRegister -> Set PortName
    asyncInputs ctr =
      case ctr of
        CellTypeAdff -> Set.fromList ["ARST"]
        CellTypeAldff -> Set.fromList ["ALOAD", "AD"]
        CellTypeDff -> Set.empty
        CellTypeDffe -> Set.empty
        CellTypeFf -> Set.empty

    cellDeps :: Cell -> [CellInstName]
    cellDeps c =
      case c ^. cellType of
        CellTypeRegister ctr ->
          -- Register cells only have direct data dependencies on
          -- their asynchronous inputs.
          Set.toAscList $ Set.fromList $
          Maybe.mapMaybe (flip Map.lookup sources) $
          concat $ Map.elems $
          flip Map.restrictKeys (asyncInputs ctr) $
          cellInputConnections c
        CellTypeUserType t
          | isMooreMachine t -> []
        _ ->
          -- For other cells, we record direct data dependencies for
          -- all input ports.
          Set.toAscList $ Set.fromList $
          Maybe.mapMaybe (flip Map.lookup sources) $
          concat $ Map.elems $ cellInputConnections c

    nodes :: [(Cell, CellInstName, [CellInstName])]
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

-- | Given a netgraph and an initial map from bit patterns to terms,
-- populate that map with terms generated from the rest of the
-- netgraph.
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
             -- NOTE: All Yosys primitive combinational cell types
             -- have a single output port named "Y".
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
           CellTypeRegister ctr ->
             -- NOTE: All Yosys primitive register cell types have a
             -- single output port named "Q".
             do bs <- lookupConn "Q"
                let width = fromIntegral (length bs)
                r <-
                  case Map.lookup cnm states of
                    Nothing ->
                      panic "netgraphToTerms" ["missing state for cell " <> cnm]
                    Just r ->
                      case ctr of
                        CellTypeAdff ->
                          -- FIXME: Parameters ARST_VALUE and
                          -- ARST_POLARITY should be arguments to
                          -- CellTypeAdff, so we don't have to parse
                          -- them in two places.
                          do let arst_value =
                                   Maybe.fromMaybe 0 $
                                   parseNat =<< Map.lookup "ARST_VALUE" (c ^. cellParameters)
                             let arst_polarity =
                                   Maybe.fromMaybe True $
                                   parseBool =<< Map.lookup "ARST_POLARITY" (c ^. cellParameters)
                             arst_value' <- SC.scBvConst sc width (fromIntegral arst_value)
                             one <- SC.scNat sc 1
                             arst_bs <- lookupConn "ARST"
                             arst <- lookupPatternTerm sc (YosysBitvecConsumerCell cnm "ARST") arst_bs acc
                             arstb <- SC.scBvNonzero sc one arst
                             -- complement reset signal if ARST_POLARITY=0
                             pos_arstb <- if arst_polarity then pure arstb else SC.scNot sc arstb
                             -- Set output to reset value on ARST; else output state value
                             ty <- SC.scBitvector sc width
                             SC.scIte sc ty pos_arstb arst_value' r

                        CellTypeAldff ->
                          do let aload_polarity =
                                   Maybe.fromMaybe True $
                                   parseBool =<< Map.lookup "ALOAD_POLARITY" (c ^. cellParameters)
                             one <- SC.scNat sc 1
                             ad_bs <- lookupConn "AD"
                             ad <- lookupPatternTerm sc (YosysBitvecConsumerCell cnm "AD") ad_bs acc
                             aload_bs <- lookupConn "ALOAD"
                             aload <- lookupPatternTerm sc (YosysBitvecConsumerCell cnm "AD") aload_bs acc
                             aloadb <- SC.scBvNonzero sc one aload
                             -- complement reset signal if ALOAD_POLARITY=0
                             pos_aloadb <- if aload_polarity then pure aloadb else SC.scNot sc aloadb
                             -- Set output to AD on ALOAD; else output state value
                             ty <- SC.scBitvector sc width
                             SC.scIte sc ty pos_aloadb ad r

                        -- For all register cell types without
                        -- asynchronous set/reset, the output is
                        -- always identical to the stored value @r@
                        -- from the state record.
                        CellTypeDff -> pure r
                        CellTypeDffe -> pure r
                        CellTypeFf -> pure r
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
-- This function should be called with a complete 'WireEnv' with
-- values for every wire, including the output wires for the given
-- cell.
cellNewState ::
  SC.SharedContext ->
  Map CellTypeName ConvertedModule ->
  WireEnv ->
  CellInstName ->
  (Cell, SC.Term) ->
  IO SC.Term
cellNewState sc env terms cnm (c, prevState) =
  case c ^. cellType of
    CellTypeRegister ctr ->
      case ctr of
        CellTypeAdff ->
          do CellTerm d width _ <- input "D" -- new value
             CellTerm q _ _ <- input "Q" -- old state value
             clk <- inputBool "CLK"
             arst <- inputBool "ARST"
             let clk_polarity = Maybe.fromMaybe True (lookupBoolParam "CLK_POLARITY")
             -- We only support CLK_POLARITY=1, i.e. posedge CLK
             unless clk_polarity $ yosysError $ YosysError "Unsupported $adff with CLK_POLARITY=0"
             let arst_value = Maybe.fromMaybe 0 (lookupNatParam "ARST_VALUE")
             -- complement reset signal if ARST_POLARITY=0
             let arst_polarity = Maybe.fromMaybe True (lookupBoolParam "ARST_POLARITY")
             pos_arst <- if arst_polarity then pure arst else SC.scNot sc arst
             arst_value' <- SC.scBvConst sc width (fromIntegral arst_value)
             ty <- SC.scBitvector sc width
             -- Set state to reset value on ARST; else if CLK then D; otherwise hold
             SC.scIte sc ty pos_arst arst_value' =<< SC.scIte sc ty clk d q
        CellTypeAldff ->
          do clk <- inputBool "CLK"
             aload <- inputBool "ALOAD"
             CellTerm ad _ _ <- input "AD" -- async load value
             CellTerm d width _ <- input "D" -- new value
             CellTerm q _ _ <- input "Q" -- old state value
             let clk_polarity = Maybe.fromMaybe True (lookupBoolParam "CLK_POLARITY")
             -- We only support CLK_POLARITY=1, i.e. posedge CLK
             unless clk_polarity $ yosysError $ YosysError "Unsupported $adff with CLK_POLARITY=0"
             -- complement aload signal if ALOAD_POLARITY=0
             let aload_polarity = Maybe.fromMaybe True (lookupBoolParam "ALOAD_POLARITY")
             pos_aload <- if aload_polarity then pure aload else SC.scNot sc aload
             ty <- SC.scBitvector sc width
             -- Set state to AD on ALOAD; else if CLK then D; otherwise hold
             SC.scIte sc ty pos_aload ad =<< SC.scIte sc ty clk d q
        CellTypeDff ->
          do CellTerm d width _ <- input "D" -- new value
             CellTerm q _ _ <- input "Q" -- old state value
             clk <- inputBool "CLK"
             let clk_polarity = Maybe.fromMaybe True (lookupBoolParam "CLK_POLARITY")
             -- We only support CLK_POLARITY=1, i.e. posedge CLK
             unless clk_polarity $ yosysError $ YosysError "Unsupported $dff with CLK_POLARITY=0"
             ty <- SC.scBitvector sc width
             SC.scIte sc ty clk d q
        CellTypeFf ->
          -- $ff cell has no CLK input; it uses the global clock, so
          -- it transitions every time step
          cellTermTerm <$> input "D"
        CellTypeDffe ->
          do CellTerm d width _ <- input "D" -- new value
             CellTerm q _ _ <- input "Q" -- old state value
             en <- inputBool "EN"
             clk <- inputBool "CLK"
             -- complement enable signal if EN_POLARITY=0
             let en_polarity = Maybe.fromMaybe True (lookupBoolParam "EN_POLARITY")
             pos_en <- if en_polarity then pure en else SC.scNot sc en
             ty <- SC.scBitvector sc width
             -- update state to D on EN & CLK; otherwise hold
             trigger <- SC.scAnd sc clk pos_en
             SC.scIte sc ty trigger d q
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
    input :: PortName -> IO CellTerm
    input portname =
      do bs <- lookupConn portname
         t <- lookupPatternTerm sc (YosysBitvecConsumerCell cnm portname) bs terms
         let signed = False -- treat as unsigned
         pure (CellTerm t (fromIntegral (length bs)) signed)
    -- | Retrieve an input of type Bool.
    inputBool :: PortName -> IO SC.Term
    inputBool portname =
      do CellTerm t _ _ <- input portname
         one <- SC.scNat sc 1
         SC.scBvNonzero sc one t
    lookupConn portname =
      case Map.lookup portname (c ^. cellConnections) of
        Nothing ->
          yosysError $
          YosysError $
          "Malformed Yosys file: Missing port " <> portname <> " for cell " <> cnm
        Just bs ->
          pure bs
    lookupNatParam :: Text.Text -> Maybe Natural
    lookupNatParam pname = parseNat =<< Map.lookup pname (c ^. cellParameters)
    lookupBoolParam :: Text.Text -> Maybe Bool
    lookupBoolParam pname = parseBool =<< Map.lookup pname (c ^. cellParameters)

-- | Parse an Aeson value as a 'Natural', if possible.
parseBool :: Aeson.Value -> Maybe Bool
parseBool (Aeson.Number n) = Just (n > 0)
parseBool (Aeson.String x) = Just (textBinNat x > 0)
parseBool _ = Nothing

-- | Parse an Aeson value as a 'Natural', if possible.
parseNat :: Aeson.Value -> Maybe Natural
parseNat (Aeson.String x) = Just (textBinNat x)
parseNat _ = Nothing

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
       registerCells :: Map CellInstName Cell
       registerCells = Map.filter cellIsRegister (m ^. moduleCells)
       registerPorts :: Map CellInstName [Bitrep]
       registerPorts = Map.mapMaybe (\c -> Map.lookup "Q" (c ^. cellConnections)) registerCells
     (stateFields1 :: Map CellInstName SC.Term) <- traverse f registerPorts

     -- Collect state types from all submodules
     let
       getSubmodule :: Cell -> Maybe ConvertedModule
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
