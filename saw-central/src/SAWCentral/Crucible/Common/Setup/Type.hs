{- |
Module      : SAWCentral.Crucible.Common.Setup.Type
Description : The CrucibleSetup monad
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE TemplateHaskell #-}

module SAWCentral.Crucible.Common.Setup.Type
  ( CrucibleSetupState(..)
  , csVarCounter
  , csPrePost
  , csResolvedState
  , csMethodSpec
  , csCrucibleContext
  , makeCrucibleSetupState
  , CrucibleSetupRO(..)
  , croTags
  , makeCrucibleSetupRO
  --
  , CrucibleSetupT
  , currentState
  , addPointsTo
  , addAllocGlobal
  , addCondition
  , freshTypedVariable
  , freshVariable
  , setupWithTag
  ) where

import           Control.Lens
import           Control.Monad.State (StateT)
import           Control.Monad.Reader (ReaderT, withReaderT)
import           Control.Monad.IO.Class (MonadIO(liftIO))
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Set (Set)
import qualified Data.Set as Set

import qualified Cryptol.TypeCheck.Type as Cryptol (Type)
import qualified CryptolSAWCore.Cryptol as Cryptol (importType, emptyEnv)
import           CryptolSAWCore.TypedTerm (TypedTerm, TypedVariable(..), typedTermOfVariable)
import           SAWCore.SharedTerm (SharedContext, scFreshVarName)

import qualified SAWCentral.Crucible.Common.MethodSpec as MS

--------------------------------------------------------------------------------
-- * CrucibleSetupT

--------------------------------------------------------------------------------
-- ** CrucibleSetupState

-- | Type of "read only" data maintained in a lexicograpic
--   manner.
data CrucibleSetupRO =
  CrucibleSetupRO
  { _croTags :: Set String
  }

makeLenses ''CrucibleSetupRO

-- | The type of state kept in the 'CrucibleSetup' monad
data CrucibleSetupState ext =
  CrucibleSetupState
  { _csVarCounter      :: !MS.AllocIndex
  , _csPrePost         :: !MS.PrePost
  , _csResolvedState   :: MS.ResolvedState ext
  , _csMethodSpec      :: MS.CrucibleMethodSpecIR ext
  , _csCrucibleContext :: MS.CrucibleContext ext
  }

makeLenses ''CrucibleSetupState

makeCrucibleSetupRO :: CrucibleSetupRO
makeCrucibleSetupRO =
  CrucibleSetupRO
  { _croTags = mempty }

makeCrucibleSetupState ::
  MS.ResolvedState ext ->
  MS.CrucibleContext ext ->
  MS.CrucibleMethodSpecIR ext ->
  CrucibleSetupState ext
makeCrucibleSetupState rs cc mspec =
  CrucibleSetupState
    { _csVarCounter      = MS.AllocIndex 0
    , _csPrePost         = MS.PreState
    , _csResolvedState   = rs
    , _csMethodSpec      = mspec
    , _csCrucibleContext = cc
    }

--------------------------------------------------------------------------------
-- ** CrucibleSetupT

type CrucibleSetupT ext m =
  ReaderT CrucibleSetupRO (StateT (CrucibleSetupState ext) m)

--------------------------------------------------------------------------------
-- ** State operations

currentState :: Lens' (CrucibleSetupState ext) (MS.StateSpec ext)
currentState f x = case x^. csPrePost of
  MS.PreState  -> csMethodSpec (MS.csPreState f) x
  MS.PostState -> csMethodSpec (MS.csPostState f) x

addPointsTo :: Monad m => MS.PointsTo ext -> CrucibleSetupT ext m ()
addPointsTo pt = currentState . MS.csPointsTos %= (pt : )

addAllocGlobal :: Monad m => MS.AllocGlobal ext -> CrucibleSetupT ext m ()
addAllocGlobal ag = csMethodSpec . MS.csGlobalAllocs %= (ag : )

addCondition :: Monad m => MS.SetupCondition ext -> CrucibleSetupT ext m ()
addCondition cond = currentState . MS.csConditions %= (cond : )

-- | Allocate a fresh variable in the form of a 'TypedVariable' and
-- record this allocation in the setup state.
freshTypedVariable ::
  MonadIO m =>
  SharedContext {- ^ shared context -} ->
  Text          {- ^ variable name  -} ->
  Cryptol.Type  {- ^ variable type  -} ->
  CrucibleSetupT arch m TypedVariable
freshTypedVariable sc name cty =
  do ty <- liftIO $ Cryptol.importType sc Cryptol.emptyEnv cty
     vn <- liftIO $ scFreshVarName sc name
     let tt = TypedVariable cty vn ty
     currentState . MS.csFreshVars %= cons tt
     return tt

-- | Allocate a fresh variable in the form of a 'TypedTerm' and record
-- this allocation in the setup state.
freshVariable ::
  MonadIO m =>
  SharedContext {- ^ shared context -} ->
  Text          {- ^ variable name  -} ->
  Cryptol.Type  {- ^ variable type  -} ->
  CrucibleSetupT arch m TypedTerm
freshVariable sc name cty =
  do tec <- freshTypedVariable sc name cty
     liftIO $ typedTermOfVariable sc tec

setupWithTag :: Text -> CrucibleSetupT arch m a -> CrucibleSetupT arch m a
setupWithTag tag m =
  withReaderT (croTags %~ Set.insert (Text.unpack tag)) m
