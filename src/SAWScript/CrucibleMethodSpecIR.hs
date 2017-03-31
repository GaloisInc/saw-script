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
 deriving (Show)


data SetupCondition where
  SetupCond_PointsTo :: SetupValue -> SetupValue -> SetupCondition
  SetupCond_Equal    :: SymType -> SetupValue -> SetupValue -> SetupCondition
 deriving (Show)


data CrucibleMethodSpecIR =
  CrucibleMethodSpec
  { csDefine         :: L.Define
  , csAllocations    :: Map AllocIndex SymType            -- ^ allocated vars
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
  , csMethodSpec    :: CrucibleMethodSpecIR
  }

initialCrucibleSetupState :: L.Define -> CrucibleSetupState
initialCrucibleSetupState def =
  CrucibleSetupState
  { csVarCounter = AllocIndex 0
  , csPrePost    = PreState
  , csMethodSpec =
    CrucibleMethodSpec
    { csDefine        = def
    , csAllocations   = Map.empty
    , csConditions    = []
    , csArgBindings   = Map.empty
    , csRetValue      = Nothing
    }
  }
