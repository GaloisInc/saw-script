{- |
Module           : $Header$
Description      : Provides typechecked representation for Crucible/LLVM function
                   specifications and function for creating it from AST
                   representation.
Stability        : provisional
Point-of-contact : atomb
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}
module SAWScript.CrucibleMethodSpecIR
where

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set


import           Lang.Crucible.LLVM.MemType
import qualified Text.LLVM.AST as L

--import qualified Verifier.LLVM.Codebase as LSS
--import qualified Lang.Crucible.LLVM.MemModel.Common as C
import SAWScript.TypedTerm

newtype AllocIndex = AllocIndex Int
  deriving (Eq, Ord, Show)

nextAllocIndex :: AllocIndex -> AllocIndex
nextAllocIndex (AllocIndex n) = AllocIndex (n + 1)

data SetupValue where
  SetupVar    :: AllocIndex -> SetupValue
  SetupTerm   :: TypedTerm -> SetupValue
  SetupStruct :: [SetupValue] -> SetupValue
  SetupArray  :: [SetupValue] -> SetupValue
  SetupNull   :: SetupValue
  SetupGlobal :: String -> SetupValue
  deriving (Show)


data PrePost
  = PreState | PostState
  deriving (Eq, Show)


data SetupCondition where
  SetupCond_PointsTo :: SetupValue -> SetupValue -> SetupCondition
  SetupCond_Equal    :: SetupValue -> SetupValue -> SetupCondition
  deriving (Show)


data CrucibleMethodSpecIR =
  CrucibleMethodSpec
  { csName           :: L.Symbol
  , csArgs           :: [L.Type]
  , csRet            :: L.Type
  , csAllocations    :: Map AllocIndex MemType            -- ^ allocated vars
  , csFreshPointers  :: Map AllocIndex MemType
  , csConditions     :: [(PrePost,SetupCondition)]        -- ^ points-to and equality statements
  , csArgBindings    :: Map Integer (SymType, SetupValue) -- ^ function arguments
  , csRetValue       :: Maybe SetupValue                  -- ^ function return value
  }
  deriving (Show)

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
    { csName          = L.defName def
    , csArgs          = L.typedType <$> L.defArgs def
    , csRet           = L.defRetType def
    , csAllocations   = Map.empty
    , csFreshPointers = Map.empty
    , csConditions    = []
    , csArgBindings   = Map.empty
    , csRetValue      = Nothing
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
    { csName          = L.decName dec
    , csArgs          = L.decArgs dec
    , csRet           = L.decRetType dec
    , csAllocations   = Map.empty
    , csFreshPointers = Map.empty
    , csConditions    = []
    , csArgBindings   = Map.empty
    , csRetValue      = Nothing
    }
  }

--------------------------------------------------------------------------------

-- | A datatype to keep track of which parts of the simulator state
-- have been initialized already.
data ResolvedState =
  ResolvedState
  { rsAllocs :: Set AllocIndex
  , rsGlobals :: Set String
  }

emptyResolvedState :: ResolvedState
emptyResolvedState = ResolvedState Set.empty Set.empty

-- | Record the initialization of the pointer represented by the given
-- SetupValue.
markResolved ::
  SetupValue ->
  ResolvedState ->
  ResolvedState
markResolved val rs =
  case val of
    SetupVar i    -> rs { rsAllocs = Set.insert i (rsAllocs rs) }
    SetupGlobal n -> rs { rsGlobals = Set.insert n (rsGlobals rs) }
    _             -> rs

-- | Test whether the pointer represented by the given SetupValue has
-- been initialized already.
testResolved ::
  SetupValue ->
  ResolvedState ->
  Bool
testResolved val rs =
  case val of
    SetupVar i    -> Set.member i (rsAllocs rs)
    SetupGlobal n -> Set.member n (rsGlobals rs)
    _             -> False
