{- |
Module      : SAWScript.Crucible.JVM.MethodSpecIR
Description : Provides type-checked representation for Crucible/JVM function
              specifications and functions for creating it from a SAWscript AST.
Maintainer  : atomb
Stability   : provisional
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
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module SAWScript.Crucible.JVM.MethodSpecIR where

import           Control.Lens
import           Control.Monad.ST (RealWorld)
import           Data.Monoid ((<>))
import qualified Text.PrettyPrint.ANSI.Leijen as PPL hiding ((<$>), (<>))

-- what4
import           What4.ProgramLoc (ProgramLoc)

import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)

-- crucible-jvm
import qualified Lang.Crucible.JVM as CJ

-- jvm-verifier
-- TODO: transition to Lang.JVM.Codebase from crucible-jvm
import qualified Verifier.Java.Codebase as CB

-- jvm-parser
import qualified Language.JVM.Parser as J

import           SAWScript.Crucible.Common (Sym)
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

type instance MS.TypeName CJ.JVM = JIdent

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

csMethodName :: Simple Lens (MS.CrucibleMethodSpecIR CJ.JVM) String
csMethodName = MS.csMethod . jvmMethodName

instance PPL.Pretty JVMMethodId where
  pretty (JVMMethodId _methName _className) = PPL.text "TODO"

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


-- TODO: We should probably use a more structured datatype (record), like in LLVM
type instance MS.AllocSpec CJ.JVM = (ProgramLoc, Allocation)

--------------------------------------------------------------------------------
-- *** PointsTo

type instance MS.PointsTo CJ.JVM = JVMPointsTo

data JVMPointsTo
  = JVMPointsToField ProgramLoc (MS.SetupValue CJ.JVM) String (MS.SetupValue CJ.JVM)
  | JVMPointsToElem ProgramLoc (MS.SetupValue CJ.JVM) Int (MS.SetupValue CJ.JVM)

ppPointsTo :: JVMPointsTo -> PPL.Doc
ppPointsTo =
  \case
    JVMPointsToField _loc ptr fld val ->
      MS.ppSetupValue ptr <> PPL.text "." <> PPL.text fld
      PPL.<+> PPL.text "points to"
      PPL.<+> MS.ppSetupValue val
    JVMPointsToElem _loc ptr idx val ->
      MS.ppSetupValue ptr <> PPL.text "[" <> PPL.text (show idx) <> PPL.text "]"
      PPL.<+> PPL.text "points to"
      PPL.<+> MS.ppSetupValue val

instance PPL.Pretty JVMPointsTo where
  pretty = ppPointsTo

--------------------------------------------------------------------------------
-- *** JVMCrucibleContext

type instance MS.Codebase CJ.JVM = CB.Codebase

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

--------------------------------------------------------------------------------

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
