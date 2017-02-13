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


import           Lang.Crucible.LLVM.DataLayout
import qualified Text.LLVM.AST as L

--import qualified Verifier.LLVM.Codebase as LSS
--import qualified Lang.Crucible.LLVM.MemModel.Common as C
import Verifier.SAW.SharedTerm -- hiding (PPOpts(..), defaultPPOpts)

data SetupValue where
  SetupReturn :: RetType -> SetupValue
  SetupVar    :: Integer -> SetupValue
  SetupTerm   :: Term -> SetupValue
  SetupStruct :: [SetupValue] -> SetupValue
  SetupArray  :: [SetupValue] -> SetupValue
  SetupNull   :: SetupValue
  SetupGlobal :: String -> SetupValue
 deriving (Show)


data PrePost
  = PreState | PostState
 deriving (Show)


data VarBinding where
  VarBind_Value       :: SetupValue -> VarBinding
  VarBind_Alloc       :: SymType -> VarBinding

instance Show VarBinding where
  show (VarBind_Value v)  = ":= " ++ show v
  show (VarBind_Alloc tp) = "{{ " ++ show (ppSymType tp) ++ " }}"

data BindingPair
  = BP !SymType !VarBinding

instance Show BindingPair where
  show (BP tp bd) = "(" ++ show (ppSymType tp) ++  ", " ++ show bd ++ ")"

newtype SetupBindings =
  SetupBindings { setupBindings :: Map Integer BindingPair }
 deriving (Show)

data SetupCondition where
  SetupCond_PointsTo :: SetupValue -> SetupValue -> SetupCondition
  SetupCond_Equal    :: SymType -> SetupValue -> SetupValue -> SetupCondition
 deriving (Show)


data CrucibleMethodSpecIR =
  CrucibleMethodSpec
  { csDefine         :: L.Define
  , csSetupBindings  :: SetupBindings
  , csConditions     :: [(PrePost,SetupCondition)]
  , csArgBindings    :: Map Integer (SymType, SetupValue)
  , csRetValue       :: Maybe BindingPair
  }
 deriving (Show)


data CrucibleSetupState =
  CrucibleSetupState
  { csVarCounter    :: !Integer
  , csPrePost       :: PrePost
  , csMethodSpec    :: CrucibleMethodSpecIR
  }

initialCrucibleSetupState :: L.Define -> CrucibleSetupState
initialCrucibleSetupState def =
  CrucibleSetupState
  { csVarCounter = 0
  , csPrePost    = PreState
  , csMethodSpec =
    CrucibleMethodSpec
    { csDefine        = def
    , csSetupBindings = SetupBindings Map.empty
    , csConditions    = []
    , csArgBindings   = Map.empty
    , csRetValue      = Nothing
    }
  }
