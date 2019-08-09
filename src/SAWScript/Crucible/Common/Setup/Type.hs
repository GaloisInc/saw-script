{- |
Module      : SAWScript.Crucible.Common.Setup.Type
Description : The CrucibleSetup monad
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module SAWScript.Crucible.Common.Setup.Type
  ( CrucibleSetupState(..)
  , csVarCounter
  , csPrePost
  , csResolvedState
  , csMethodSpec
  , csCrucibleContext
  , makeCrucibleSetupState
  --
  , CrucibleSetupT
  , currentState
  , addPointsTo
  , addCondition
  , addGhostCondition
  , freshVariable
  ) where

import           Control.Lens
import           Control.Monad.State (StateT)
import           Control.Monad.IO.Class (MonadIO(liftIO))

import           Verifier.SAW.TypedTerm (TypedTerm, mkTypedTerm)
import           Verifier.SAW.SharedTerm (Term, SharedContext, scFreshGlobal)

import qualified SAWScript.Crucible.Common.MethodSpec as MS

--------------------------------------------------------------------------------
-- * CrucibleSetupT

--------------------------------------------------------------------------------
-- ** CrucibleSetupState

-- | The type of state kept in the 'CrucibleSetup' monad
data CrucibleSetupState ext =
  CrucibleSetupState
  { _csVarCounter      :: !MS.AllocIndex
  , _csPrePost         :: !MS.PrePost
  , _csResolvedState   :: MS.ResolvedState
  , _csMethodSpec      :: MS.CrucibleMethodSpecIR ext
  , _csCrucibleContext :: MS.CrucibleContext ext
  }

makeLenses ''CrucibleSetupState

makeCrucibleSetupState ::
  MS.CrucibleContext ext ->
  MS.CrucibleMethodSpecIR ext ->
  CrucibleSetupState ext
makeCrucibleSetupState cc mspec =
  CrucibleSetupState
    { _csVarCounter      = MS.AllocIndex 0
    , _csPrePost         = MS.PreState
    , _csResolvedState   = MS.emptyResolvedState
    , _csMethodSpec      = mspec
    , _csCrucibleContext = cc
    }

--------------------------------------------------------------------------------
-- ** CrucibleSetupT

type CrucibleSetupT ext = StateT (CrucibleSetupState ext)

--------------------------------------------------------------------------------
-- ** State operations

currentState :: Lens' (CrucibleSetupState ext) (MS.StateSpec ext)
currentState f x = case x^. csPrePost of
  MS.PreState  -> csMethodSpec (MS.csPreState f) x
  MS.PostState -> csMethodSpec (MS.csPostState f) x

addPointsTo :: Monad m => MS.PointsTo ext -> CrucibleSetupT ext m ()
addPointsTo pt = currentState . MS.csPointsTos %= (pt : )

addCondition :: Monad m => MS.SetupCondition ext -> CrucibleSetupT ext m ()
addCondition cond = currentState . MS.csConditions %= (cond : )

addGhostCondition :: Monad m => MS.GhostCondition -> CrucibleSetupT ext m ()
addGhostCondition cond = currentState . MS.csGhostConditions %= (cond : )

-- | Allocated a fresh variable and record this allocation in the
-- setup state.
freshVariable ::
  MonadIO m =>
  SharedContext {- ^ shared context -} ->
  String        {- ^ variable name  -} ->
  Term          {- ^ variable type  -} ->
  CrucibleSetupT arch m TypedTerm
freshVariable sc name ty =
  do tt <- liftIO (mkTypedTerm sc =<< scFreshGlobal sc name ty)
     currentState . MS.csFreshVars %= cons tt
     return tt
