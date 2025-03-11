{- |
Module      : SAWCentral.Crucible.Common.Builtins
Description : User-facing operations in the CrucibleSetup monad
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ParallelListComp #-}

module SAWCentral.Crucible.Common.Setup.Builtins
  ( crucible_precond
  , crucible_postcond
  , crucible_return
  , crucible_execute_func
  , crucible_equal
  , CheckPointsToType(..)
  ) where

import           Control.Lens
import           Control.Monad (when)
import           Control.Monad.State (get)
import qualified Data.Map as Map

import qualified What4.ProgramLoc as W4

import           Verifier.SAW.TypedTerm (TypedTerm)

import           SAWScript.Value

import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import           SAWCentral.Crucible.Common.Setup.Type

--------------------------------------------------------------------------------
-- ** Builtins

-- TODO: crucible_fresh_var?

crucible_precond ::
  W4.ProgramLoc ->
  TypedTerm ->
  CrucibleSetup ext ()
crucible_precond loc p = do
  st <- get
  tags <- view croTags
  let md = MS.ConditionMetadata
           { MS.conditionLoc = loc
           , MS.conditionTags = tags
           , MS.conditionType = "specification assertion"
           , MS.conditionContext = ""
           }
  when (st ^. csPrePost == MS.PostState) $
    fail "attempt to use `crucible_precond` in post state"
  addCondition (MS.SetupCond_Pred md p)

crucible_postcond ::
  W4.ProgramLoc ->
  TypedTerm ->
  CrucibleSetup ext ()
crucible_postcond loc p = do
  st <- get
  tags <- view croTags
  let md = MS.ConditionMetadata
           { MS.conditionLoc = loc
           , MS.conditionTags = tags
           , MS.conditionType = "specification assertion"
           , MS.conditionContext = ""
           }
  when (st ^. csPrePost == MS.PreState) $
    fail "attempt to use `crucible_postcond` in pre state"
  addCondition (MS.SetupCond_Pred md p)

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

crucible_equal ::
  W4.ProgramLoc ->
  MS.SetupValue ext ->
  MS.SetupValue ext ->
  CrucibleSetup ext ()
crucible_equal loc val1 val2 = do
  tags <- view croTags
  let md = MS.ConditionMetadata
           { MS.conditionLoc = loc
           , MS.conditionTags = tags
           , MS.conditionType = "equality specification"
           , MS.conditionContext = ""
           }
  addCondition (MS.SetupCond_Equal md val1 val2)

--------------------------------------------------------------------------------
-- ** Shared data types

-- | When invoking a points-to command, against what should SAW check the type
-- of the RHS value?
data CheckPointsToType ty
  = CheckAgainstPointerType
    -- ^ Check the type of the RHS value against the type that the LHS points to.
    --   Used by commands such as @llvm_{conditional_}points_to@ and
    --   @mir_points_to@.
  | CheckAgainstCastedType ty
    -- ^ Check the type of the RHS value against the provided @ty@, which
    --   the LHS pointer is casted to.
    --   This is currently used by @llvm_{conditional_}points_to_at_type@ only.
  deriving (Functor, Foldable, Traversable)
