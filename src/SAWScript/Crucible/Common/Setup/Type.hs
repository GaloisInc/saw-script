{- |

Module      : SAWScript.Crucible.Common.Setup.Type
Description : The CrucibleSetup monad
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
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
  -- , runCrucibleSetupT
  -- , execCrucibleSetupT
  -- , underCrucibleSetupT
  , currentState
  , addPointsTo
  , addCondition
  , freshVariable
  ) where

import           Data.Coerce (coerce)
import           GHC.Generics (Generic, Generic1)
import           Control.Lens
import           Control.Monad.State (MonadState, StateT(..), runStateT, execStateT)
import           Control.Monad.IO.Class (MonadIO(liftIO))

import           Verifier.SAW.TypedTerm (TypedTerm, mkTypedTerm)
import           Verifier.SAW.SharedTerm (Term, SharedContext, scFreshGlobal)

import           SAWScript.Crucible.Common
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

-- newtype CrucibleSetupT ext m a =
--   CrucibleSetupT
--     { unCrucibleSetupT :: StateT (CrucibleSetupState ext) m a }
--   deriving ( Applicative
--            , Functor
--            , Generic
--            , Generic1
--            , Monad
--            , MonadFail
--            , MonadIO
--            )

-- deriving instance Monad m =>
--   MonadState (CrucibleSetupState ext) (CrucibleSetupT ext m)

-- instance MonadTrans (CrucibleSetupT ext) where
--   lift = CrucibleSetupT . lift

-- execCrucibleSetupT ::
--   Monad m =>
--   CrucibleSetupT ext m a ->
--   CrucibleSetupState ext ->
--   m (CrucibleSetupState ext)
-- execCrucibleSetupT (CrucibleSetupT action) = execStateT action

-- runCrucibleSetupT ::
--   Monad m =>
--   CrucibleSetupT ext m a ->
--   CrucibleSetupState ext ->
--   m (a, CrucibleSetupState ext)
-- runCrucibleSetupT (CrucibleSetupT action) = runStateT action

-- underCrucibleSetupT ::
--   (forall b. m b -> m b) ->
--   CrucibleSetupT ext m a ->
--   CrucibleSetupT ext m a
-- underCrucibleSetupT doUnder action = CrucibleSetupT $ StateT $ \s ->
--   doUnder (runStateT (unCrucibleSetupT action) s)

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
