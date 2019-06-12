{- |
Module      : SAWScript.Crucible.JVM.MethodSpecIR
Description : Provides type-checked representation for Crucible/JVM function
              specifications and functions for creating it from a SAWscript AST.
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module SAWScript.Crucible.JVM.MethodSpecIR where

import           Control.Lens
import           Control.Monad.ST (RealWorld)
import           Control.Monad.Trans (lift)
import           Control.Monad.Trans.Maybe
import           Data.IORef
import           Data.Map (Map)
import           Data.Monoid ((<>))
import qualified Data.Map as Map
import qualified Text.PrettyPrint.ANSI.Leijen as PPL hiding ((<$>), (<>))

-- what4
import qualified What4.Expr.Builder as B
import           What4.ProgramLoc (ProgramLoc)

import qualified Lang.Crucible.Types as Crucible
  (IntrinsicType, EmptyCtx)
import qualified Lang.Crucible.CFG.Common as Crucible (GlobalVar)
import qualified Lang.Crucible.Backend.SAWCore as Crucible
  (SAWCoreBackend, saw_ctx, toSC)
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)
import qualified Lang.Crucible.Simulator.Intrinsics as Crucible
  (IntrinsicClass(Intrinsic, muxIntrinsic){-, IntrinsicMuxFn(IntrinsicMuxFn)-})

-- crucible-jvm
import qualified Lang.Crucible.JVM as CJ

-- jvm-verifier
-- TODO: transition to Lang.JVM.Codebase from crucible-jvm
import qualified Verifier.Java.Codebase as CB

-- jvm-parser
import qualified Language.JVM.Parser as J

-- saw-core
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm

import SAWScript.Options
import SAWScript.Prover.SolverStats

import           SAWScript.Crucible.Common (AllocIndex(..), PrePost(..), Sym)
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Setup.Type as Setup

--------------------------------------------------------------------------------
-- ** Language features

type instance MS.HasSetupNull CJ.JVM = 'True
type instance MS.HasSetupGlobal CJ.JVM = 'True
type instance MS.HasSetupStruct CJ.JVM = 'False
type instance MS.HasSetupArray CJ.JVM = 'False
type instance MS.HasSetupElem CJ.JVM = 'False
type instance MS.HasSetupField CJ.JVM = 'False
type instance MS.HasSetupGlobalInitializer CJ.JVM = 'False

type instance MS.HasGhostState CJ.JVM = 'False

type JIdent = String -- FIXME(huffman): what to put here?

type instance MS.TypeName ext = JIdent

type instance MS.ExtType CJ.JVM = J.Type

--------------------------------------------------------------------------------
-- *** JVMMethodId

data JVMMethodId =
  JVMMethodId
    { _jvmMethodName :: String
    , _jvmClassName  :: J.ClassName
    }
  deriving (Eq, Ord, Show)

makeLenses ''JVMMethodId

instance PPL.Pretty JVMMethodId where
  pretty (JVMMethodId methName className) = PPL.text "TODO"

type instance MS.MethodId CJ.JVM = JVMMethodId

--------------------------------------------------------------------------------
-- *** Allocation

data Allocation
  = AllocObject J.ClassName
  | AllocArray Int J.Type
  deriving (Eq, Ord, Show)

allocationType :: Allocation -> J.Type
allocationType alloc =
  case alloc of
    AllocObject cname -> J.ClassType cname
    AllocArray _len ty -> J.ArrayType ty


type instance MS.AllocSpec CJ.JVM = Allocation

--------------------------------------------------------------------------------
-- *** JVMModule

-- data JVMModule arch =
--   JVMModule
--   { _modName :: String
--   , _modAST :: L.Module
--   , _modTrans :: CL.ModuleTranslation arch
--   }

-- makeLenses ''JVMModule

type instance MS.Codebase CJ.JVM = CB.Codebase

{-
-- | Represent `CrucibleMethodSpecIR` as a function term in SAW-Core.
methodSpecToTerm :: SharedContext -> CrucibleMethodSpecIR -> MaybeT IO Term
methodSpecToTerm sc spec =
      -- 1. fill in the post-state user variable holes with final
      -- symbolic state
  let _ppts = _csPointsTos $ _csPostState $ instantiateUserVars spec
      -- 2. get the free variables in post points to's (note: these
      -- should be contained in variables bound by pre-points-tos)

      -- 3. abstract the free variables in each post-points-to

      -- 4. put every abstracted post-points-to in a tuple

      -- 5. Create struct type with fields being names of free variables

      -- 6. Create a lambda term bound to a struct-typed variable that returns the tuple
  in lift $ scLambda sc undefined undefined undefined

-- | Rewrite the `csPostPointsTos` to substitute the elements of the
-- final symbolic state for the fresh variables created by the user in
-- the post-state.
instantiateUserVars :: CrucibleMethodSpecIR -> CrucibleMethodSpecIR
instantiateUserVars _spec = undefined
-}

-- -- | A datatype to keep track of which parts of the simulator state
-- -- have been initialized already. For each allocation unit or global,
-- -- we keep a list of element-paths that identify the initialized
-- -- sub-components.
-- data ResolvedState =
--   ResolvedState
--   { _rsAllocs :: Map AllocIndex [Either String Int]
--   , _rsGlobals :: Map String [Either String Int]
--   }

data JVMCrucibleContext =
  JVMCrucibleContext
  { _jccJVMClass       :: J.Class
  , _jccCodebase       :: CB.Codebase
  , _jccJVMContext     :: CJ.JVMContext
  , _jccBackend        :: Sym -- This is stored inside field _ctxSymInterface of Crucible.SimContext; why do we need another one?
  , _jccHandleAllocator :: Crucible.HandleAllocator RealWorld
  }

makeLenses ''JVMCrucibleContext

type instance MS.CrucibleContext CJ.JVM = JVMCrucibleContext

--------------------------------------------------------------------------------

initialDefCrucibleMethodSpecIR ::
  CB.Codebase ->
  J.ClassName ->
  J.Method ->
  ProgramLoc ->
  MS.CrucibleMethodSpecIR CJ.JVM
initialDefCrucibleMethodSpecIR cb cname method loc =
  let methId = JVMMethodId (J.methodName method) cname
      retTy = J.methodReturnType method
      argTys = thisType ++ J.methodParameterTypes method
  in MS.makeCrucibleMethodSpecIR methId argTys retTy loc cb
  where thisType = if J.methodIsStatic method then [] else [J.ClassType cname]

initialCrucibleSetupState ::
  JVMCrucibleContext ->
  J.Method ->
  ProgramLoc ->
  Setup.CrucibleSetupState CJ.JVM
initialCrucibleSetupState cc method loc =
  Setup.makeCrucibleSetupState cc $
    initialDefCrucibleMethodSpecIR
      (cc ^. jccCodebase)
      (J.className $ cc ^. jccJVMClass)
      method
      loc
