{- |
Module      : SAWScript.Crucible.Common.Builtins
Description : User-facing operations in the CrucibleSetup monad
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE ParallelListComp #-}

module SAWScript.Crucible.Common.Setup.Builtins where

import           Control.Lens
import           Control.Monad (when)
import           Control.Monad.State (get)
import qualified Data.Map as Map

import qualified What4.ProgramLoc as W4

import           Verifier.SAW.TypedTerm (TypedTerm)

import           SAWScript.Value

import qualified SAWScript.Crucible.Common.MethodSpec as MS
import           SAWScript.Crucible.Common.Setup.Type

--------------------------------------------------------------------------------
-- ** Builtins

-- TODO: crucible_fresh_var?

crucible_precond ::
  W4.ProgramLoc ->
  TypedTerm ->
  CrucibleSetup ext ()
crucible_precond loc p = do
  st <- get
  when (st ^. csPrePost == MS.PostState) $
    fail "attempt to use `crucible_precond` in post state"
  addCondition (MS.SetupCond_Pred loc p)

crucible_postcond ::
  W4.ProgramLoc ->
  TypedTerm ->
  CrucibleSetup ext ()
crucible_postcond loc p = do
  st <- get
  when (st ^. csPrePost == MS.PreState) $
    fail "attempt to use `crucible_postcond` in pre state"
  addCondition (MS.SetupCond_Pred loc p)

crucible_return ::
  MS.SetupValue ext ->
  CrucibleSetup ext ()
crucible_return retval = do
  ret <- use (csMethodSpec . MS.csRetValue)
  case ret of
    Just _ -> fail "crucible_return: duplicate return value specification"
    Nothing -> csMethodSpec . MS.csRetValue .= Just retval

crucible_execute_func ::
  [MS.SetupValue ext] ->
  CrucibleSetup ext ()
crucible_execute_func args = do
  tps <- use (csMethodSpec . MS.csArgs)
  csPrePost .= MS.PostState
  csMethodSpec . MS.csArgBindings .= Map.fromList [ (i, (t,a))
                                                  | i <- [0..]
                                                  | a <- args
                                                  | t <- tps
                                                  ]
