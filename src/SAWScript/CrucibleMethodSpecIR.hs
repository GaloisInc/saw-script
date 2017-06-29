{- |
Module      : $Header$
Description : Provides typechecked representation for Crucible/LLVM function
              specifications and function for creating it from AST
              representation.
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}
module SAWScript.CrucibleMethodSpecIR where

import           Data.List (isPrefixOf)
import           Data.Map (Map)
import qualified Data.Map as Map


import           Lang.Crucible.LLVM.MemType
import qualified Text.LLVM.AST as L
import           Data.IORef

import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as Crucible

import qualified Lang.Crucible.LLVM.Intrinsics as Crucible
import qualified Lang.Crucible.Types as Crucible
import qualified Lang.Crucible.CFG.Common as Crucible
--import qualified Verifier.LLVM.Codebase as LSS
--import qualified Lang.Crucible.LLVM.MemModel.Common as C
import SAWScript.SolverStats
import SAWScript.TypedTerm

import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
import qualified Lang.Crucible.Solver.SAWCoreBackend as Crucible
import qualified Lang.Crucible.Solver.SimpleBuilder as Crucible
import Verifier.SAW.SharedTerm

newtype AllocIndex = AllocIndex Int
  deriving (Eq, Ord, Show)

nextAllocIndex :: AllocIndex -> AllocIndex
nextAllocIndex (AllocIndex n) = AllocIndex (n + 1)

data SetupValue where
  SetupVar    :: AllocIndex -> SetupValue
  SetupTerm   :: TypedTerm -> SetupValue
  SetupStruct :: [SetupValue] -> SetupValue
  SetupArray  :: [SetupValue] -> SetupValue
  SetupElem   :: SetupValue -> Int -> SetupValue
  SetupNull   :: SetupValue
  SetupGlobal :: String -> SetupValue
  deriving (Show)


data PrePost
  = PreState | PostState
  deriving (Eq, Show)


data PointsTo = PointsTo SetupValue SetupValue
  deriving (Show)

data SetupCondition where
  SetupCond_Equal    :: SetupValue -> SetupValue -> SetupCondition
  SetupCond_Pred     :: TypedTerm -> SetupCondition
  SetupCond_Ghost    :: Crucible.GlobalVar (Crucible.IntrinsicType GhostValue) ->
                        TypedTerm ->
                        SetupCondition
  deriving (Show)


data CrucibleMethodSpecIR =
  CrucibleMethodSpec
  { csName            :: L.Symbol
  , csArgs            :: [L.Type]
  , csRet             :: L.Type
  , csPreAllocations  :: Map AllocIndex MemType            -- ^ vars allocated before the function runs
  , csPostAllocations :: Map AllocIndex MemType            -- ^ vars allocated by the function itself
  , csFreshPointers   :: Map AllocIndex MemType
  , csPrePointsTos    :: [PointsTo]                        -- ^ points-to statements from the pre-state section
  , csPostPointsTos   :: [PointsTo]                        -- ^ points-to statements from the post-state section
  , csConditions      :: [(PrePost, SetupCondition)]       -- ^ equality and precond/postcond statements
  , csArgBindings     :: Map Integer (SymType, SetupValue) -- ^ function arguments
  , csRetValue        :: Maybe SetupValue                  -- ^ function return value
  , csSolverStats     :: SolverStats                       -- ^ statistics about the proof that produced this
  }
  deriving (Show)

csAllocations :: CrucibleMethodSpecIR -> Map AllocIndex MemType
csAllocations cs = Map.union (csPreAllocations cs) (csPostAllocations cs)

csPreconditions :: CrucibleMethodSpecIR -> [SetupCondition]
csPreconditions cs = [ c | (PreState, c) <- csConditions cs ]

csPostconditions :: CrucibleMethodSpecIR -> [SetupCondition]
csPostconditions cs = [ c | (PostState, c) <- csConditions cs ]

data CrucibleSetupState =
  CrucibleSetupState
  { csVarCounter    :: !AllocIndex
  , csPrePost       :: PrePost
  , csResolvedState :: ResolvedState
  , csMethodSpec    :: CrucibleMethodSpecIR
  }

initialCrucibleSetupState :: L.Define -> CrucibleSetupState
initialCrucibleSetupState def =
  CrucibleSetupState
  { csVarCounter    = AllocIndex 0
  , csPrePost       = PreState
  , csResolvedState = emptyResolvedState
  , csMethodSpec    =
    CrucibleMethodSpec
    { csName            = L.defName def
    , csArgs            = L.typedType <$> L.defArgs def
    , csRet             = L.defRetType def
    , csPreAllocations  = Map.empty
    , csPostAllocations = Map.empty
    , csFreshPointers   = Map.empty
    , csPrePointsTos    = []
    , csPostPointsTos   = []
    , csConditions      = []
    , csArgBindings     = Map.empty
    , csRetValue        = Nothing
    , csSolverStats     = mempty
    }
  }

initialCrucibleSetupStateDecl :: L.Declare -> CrucibleSetupState
initialCrucibleSetupStateDecl dec =
  CrucibleSetupState
  { csVarCounter    = AllocIndex 0
  , csPrePost       = PreState
  , csResolvedState = emptyResolvedState
  , csMethodSpec    =
    CrucibleMethodSpec
    { csName            = L.decName dec
    , csArgs            = L.decArgs dec
    , csRet             = L.decRetType dec
    , csPreAllocations  = Map.empty
    , csPostAllocations = Map.empty
    , csFreshPointers   = Map.empty
    , csPrePointsTos    = []
    , csPostPointsTos   = []
    , csConditions      = []
    , csArgBindings     = Map.empty
    , csRetValue        = Nothing
    , csSolverStats     = mempty
    }
  }

--------------------------------------------------------------------------------

-- | A datatype to keep track of which parts of the simulator state
-- have been initialized already. For each allocation unit or global,
-- we keep a list of element-paths that identify the initialized
-- sub-components.
data ResolvedState =
  ResolvedState
  { rsAllocs :: Map AllocIndex [[Int]]
  , rsGlobals :: Map String [[Int]]
  }

emptyResolvedState :: ResolvedState
emptyResolvedState = ResolvedState Map.empty Map.empty

-- | Record the initialization of the pointer represented by the given
-- SetupValue.
markResolved ::
  SetupValue ->
  ResolvedState ->
  ResolvedState
markResolved val0 rs = go [] val0
  where
    go path val =
      case val of
        SetupVar n    -> rs { rsAllocs = Map.alter (ins path) n (rsAllocs rs) }
        SetupGlobal c -> rs { rsGlobals = Map.alter (ins path) c (rsGlobals rs) }
        SetupElem v i -> go (i : path) v
        _             -> rs

    ins path Nothing = Just [path]
    ins path (Just paths) = Just (path : paths)

-- | Test whether the pointer represented by the given SetupValue has
-- been initialized already.
testResolved ::
  SetupValue ->
  ResolvedState ->
  Bool
testResolved val0 rs = go [] val0
  where
    go path val =
      case val of
        SetupVar n    -> test path (Map.lookup n (rsAllocs rs))
        SetupGlobal c -> test path (Map.lookup c (rsGlobals rs))
        SetupElem v i -> go (i : path) v
        _             -> False

    test _ Nothing = False
    test path (Just paths) = any (`isPrefixOf` path) paths


type GhostValue = "GhostValue"
instance Crucible.IntrinsicClass (Crucible.SAWCoreBackend n) GhostValue where
  type Intrinsic (Crucible.SAWCoreBackend n) GhostValue = TypedTerm
  muxIntrinsic sym _namerep prd thn els =
    do st <- readIORef (Crucible.sbStateManager sym)
       let sc  = Crucible.saw_ctx st
       prd' <- Crucible.toSC sym prd
       typ  <- scTypeOf sc (ttTerm thn)
       res  <- scIte sc typ prd' (ttTerm thn) (ttTerm els)
       return thn { ttTerm = res }

intrinsics :: MapF.MapF Crucible.SymbolRepr (Crucible.IntrinsicMuxFn
                (Crucible.SAWCoreBackend Crucible.GlobalNonceGenerator))
intrinsics =
  MapF.insert
    (Crucible.knownSymbol :: Crucible.SymbolRepr GhostValue)
    Crucible.IntrinsicMuxFn
    Crucible.llvmIntrinsicTypes
