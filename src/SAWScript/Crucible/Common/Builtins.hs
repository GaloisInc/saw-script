{-# LANGUAGE OverloadedStrings #-}

module SAWScript.Crucible.Common.Builtins
  ( crucible_declare_ghost_state
  , crucible_ghost_value
  ) where

import Control.Monad.IO.Class(liftIO)
import qualified Data.Text as Text

import qualified Lang.Crucible.CFG.Core as Crucible

import Verifier.SAW.TypedTerm (TypedTerm)

import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Setup.Type as Setup

import SAWScript.Options
import SAWScript.Value

crucible_declare_ghost_state ::
  BuiltinContext ->
  Options        ->
  String         ->
  TopLevel Value
crucible_declare_ghost_state _bic _opt name =
  do allocator <- getHandleAlloc
     global <- liftIO (Crucible.freshGlobalVar allocator (Text.pack name) Crucible.knownRepr)
     return (VGhostVar global)

crucible_ghost_value ::
  MS.GhostGlobal ->
  TypedTerm      ->
  Setup.CrucibleSetupT ext TopLevel ()
crucible_ghost_value ghost val =
  do loc <- getW4Position "crucible_ghost_value"
     Setup.addGhostCondition (MS.GhostCondition loc ghost val)
