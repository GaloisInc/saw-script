{- |
Module      : SAWScript.Crucible.JVM.Setup.Value
Description : Data types and type family instances for JVM-specific code
License     : BSD3
Maintainer  : Ryan Scott <rscott@galois.com>
Stability   : provisional

The module exists separately from "SAWScript.Crucible.JVM.MethodSpecIR"
primarily to avoid import cycles. You probably want to import
"SAWScript.Crucible.JVM.MethodSpecIR" (which re-exports everything from this
module, plus additional functionality) instead.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Crucible.JVM.Setup.Value
  ( JIdent

  , JVMMethodId(..)
  , jvmMethodKey
  , jvmClassName

  , Allocation(..)

  , JVMPointsTo(..)

  , JVMCrucibleContext(..)
  , jccJVMClass
  , jccCodebase
  , jccJVMContext
  , jccBackend
  , jccHandleAllocator

  , JVMRefVal
  ) where

import           Control.Lens
import qualified Prettyprinter as PPL

import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)

-- crucible-jvm
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.JVM as CJ
import qualified Lang.JVM.Codebase as CB

-- jvm-parser
import qualified Language.JVM.Parser as J

-- cryptol-saw-core
import           Verifier.SAW.TypedTerm (TypedTerm)

import           SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.Setup.Value as MS

--------------------------------------------------------------------------------
-- ** Language features

type instance MS.HasSetupNull CJ.JVM = 'True
type instance MS.HasSetupGlobal CJ.JVM = 'False
type instance MS.HasSetupStruct CJ.JVM = 'False
type instance MS.HasSetupArray CJ.JVM = 'False
type instance MS.HasSetupElem CJ.JVM = 'False
type instance MS.HasSetupField CJ.JVM = 'False
type instance MS.HasSetupCast CJ.JVM = 'False
type instance MS.HasSetupUnion CJ.JVM = 'False
type instance MS.HasSetupGlobalInitializer CJ.JVM = 'False

type instance MS.HasGhostState CJ.JVM = 'False

type JIdent = String -- FIXME(huffman): what to put here?

type instance MS.TypeName CJ.JVM = JIdent

type instance MS.ExtType CJ.JVM = J.Type
type instance MS.CastType CJ.JVM = ()
type instance MS.ResolvedState CJ.JVM = ()

--------------------------------------------------------------------------------
-- *** JVMMethodId

data JVMMethodId =
  JVMMethodId
    { _jvmMethodKey :: J.MethodKey
    , _jvmClassName  :: J.ClassName
    }
  deriving (Eq, Ord, Show)

makeLenses ''JVMMethodId

-- TODO: avoid intermediate 'String' values
instance PPL.Pretty JVMMethodId where
  pretty (JVMMethodId methKey className) =
    PPL.pretty (concat [J.unClassName className ,".", J.methodKeyName methKey])

type instance MS.MethodId CJ.JVM = JVMMethodId

--------------------------------------------------------------------------------
-- *** Allocation

data Allocation
  = AllocObject J.ClassName
  | AllocArray Int J.Type
  deriving (Eq, Ord, Show)

-- TODO: We should probably use a more structured datatype (record), like in LLVM
type instance MS.AllocSpec CJ.JVM = (MS.ConditionMetadata, Allocation)

--------------------------------------------------------------------------------
-- *** PointsTo

type instance MS.PointsTo CJ.JVM = JVMPointsTo

data JVMPointsTo
  = JVMPointsToField MS.ConditionMetadata MS.AllocIndex J.FieldId (Maybe (MS.SetupValue CJ.JVM))
  | JVMPointsToStatic MS.ConditionMetadata J.FieldId (Maybe (MS.SetupValue CJ.JVM))
  | JVMPointsToElem MS.ConditionMetadata MS.AllocIndex Int (Maybe (MS.SetupValue CJ.JVM))
  | JVMPointsToArray MS.ConditionMetadata MS.AllocIndex (Maybe TypedTerm)

--------------------------------------------------------------------------------
-- *** JVMCrucibleContext

type instance MS.Codebase CJ.JVM = CB.Codebase

data JVMCrucibleContext =
  JVMCrucibleContext
  { _jccJVMClass       :: J.Class
  , _jccCodebase       :: CB.Codebase
  , _jccJVMContext     :: CJ.JVMContext
  , _jccBackend        :: SomeOnlineBackend
  , _jccHandleAllocator :: Crucible.HandleAllocator
  }

makeLenses ''JVMCrucibleContext

type instance MS.CrucibleContext CJ.JVM = JVMCrucibleContext

--------------------------------------------------------------------------------
-- *** Pointers

type instance MS.Pointer' CJ.JVM Sym = JVMRefVal

type JVMRefVal = CS.RegValue Sym CJ.JVMRefType
