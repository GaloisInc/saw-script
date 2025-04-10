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

module SAWScript.Crucible.JVM.MethodSpecIR
  ( JIdent

  , JVMMethodId(..)
  , jvmMethodKey
  , jvmClassName
  , jvmMethodName
  , csMethodKey
  , csMethodName

  , Allocation(..)
  , allocationType

  , JVMPointsTo(..)
  , overlapPointsTo
  , ppPointsTo

  , JVMCrucibleContext(..)
  , jccJVMClass
  , jccCodebase
  , jccJVMContext
  , jccBackend
  , jccHandleAllocator
  , jccWithBackend
  , jccSym

  , initialDefCrucibleMethodSpecIR
  , initialCrucibleSetupState

  , intrinsics
  ) where

import           Control.Lens
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.SymbolRepr (SymbolRepr, knownSymbol)
import qualified Prettyprinter as PPL

-- what4
import           What4.ProgramLoc (ProgramLoc)

-- crucible-jvm
import qualified Lang.Crucible.JVM as CJ
import qualified Lang.Crucible.Simulator.Intrinsics as CS
  (IntrinsicMuxFn(IntrinsicMuxFn))
import qualified Lang.JVM.Codebase as CB

-- jvm-parser
import qualified Language.JVM.Parser as J

import           SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Setup.Type as Setup
import           SAWScript.Crucible.JVM.Setup.Value

--------------------------------------------------------------------------------
-- *** JVMMethodId

jvmMethodName :: Getter JVMMethodId String
jvmMethodName = jvmMethodKey . to J.methodKeyName

csMethodKey :: Lens' (MS.CrucibleMethodSpecIR CJ.JVM) J.MethodKey
csMethodKey = MS.csMethod . jvmMethodKey

csMethodName :: Getter (MS.CrucibleMethodSpecIR CJ.JVM) String
csMethodName = MS.csMethod . jvmMethodName

--------------------------------------------------------------------------------
-- *** Allocation

allocationType :: Allocation -> J.Type
allocationType alloc =
  case alloc of
    AllocObject cname -> J.ClassType cname
    AllocArray _len ty -> J.ArrayType ty

--------------------------------------------------------------------------------
-- *** PointsTo

overlapPointsTo :: JVMPointsTo -> JVMPointsTo -> Bool
overlapPointsTo =
  \case
    JVMPointsToField _ p1 f1 _ ->
      \case
        JVMPointsToField _ p2 f2 _ -> p1 == p2 && f1 == f2
        _                          -> False
    JVMPointsToStatic _ f1 _ ->
      \case
        JVMPointsToStatic _ f2 _   -> f1 == f2
        _                          -> False
    JVMPointsToElem _ p1 i1 _ ->
      \case
        JVMPointsToElem _ p2 i2 _  -> p1 == p2 && i1 == i2
        JVMPointsToArray _ p2 _    -> p1 == p2
        _                          -> False
    JVMPointsToArray _ p1 _ ->
      \case
        JVMPointsToElem _ p2 _ _   -> p1 == p2
        JVMPointsToArray _ p2 _    -> p1 == p2
        _                          -> False

ppPointsTo :: JVMPointsTo -> PPL.Doc ann
ppPointsTo =
  \case
    JVMPointsToField _loc ptr fid val ->
      MS.ppAllocIndex ptr <> PPL.pretty "." <> PPL.pretty (J.fieldIdName fid)
      PPL.<+> PPL.pretty "points to"
      PPL.<+> opt MS.ppSetupValue val
    JVMPointsToStatic _loc fid val ->
      PPL.pretty (J.unClassName (J.fieldIdClass fid)) <> PPL.pretty "." <> PPL.pretty (J.fieldIdName fid)
      PPL.<+> PPL.pretty "points to"
      PPL.<+> opt MS.ppSetupValue val
    JVMPointsToElem _loc ptr idx val ->
      MS.ppAllocIndex ptr <> PPL.pretty "[" <> PPL.pretty idx <> PPL.pretty "]"
      PPL.<+> PPL.pretty "points to"
      PPL.<+> opt MS.ppSetupValue val
    JVMPointsToArray _loc ptr val ->
      MS.ppAllocIndex ptr
      PPL.<+> PPL.pretty "points to"
      PPL.<+> opt MS.ppTypedTerm val
  where
    opt = maybe (PPL.pretty "<unspecified>")

instance PPL.Pretty JVMPointsTo where
  pretty = ppPointsTo

--------------------------------------------------------------------------------
-- *** JVMCrucibleContext

jccWithBackend ::
  JVMCrucibleContext ->
  (forall solver. OnlineSolver solver => Backend solver -> a) ->
  a
jccWithBackend cc k =
  case cc^.jccBackend of SomeOnlineBackend bak -> k bak

jccSym :: Getter JVMCrucibleContext Sym
jccSym = to (\jcc -> jccWithBackend jcc backendGetSym)

--------------------------------------------------------------------------------

initialDefCrucibleMethodSpecIR ::
  CB.Codebase ->
  J.ClassName ->
  J.Method ->
  ProgramLoc ->
  MS.CrucibleMethodSpecIR CJ.JVM
initialDefCrucibleMethodSpecIR cb cname method loc =
  let methId = JVMMethodId (J.methodKey method) cname
      retTy = J.methodReturnType method
      argTys = thisType ++ J.methodParameterTypes method
  in MS.makeCrucibleMethodSpecIR methId argTys retTy loc cb
  where thisType = if J.methodIsStatic method then [] else [J.ClassType cname]

initialCrucibleSetupState ::
  JVMCrucibleContext ->
  (J.Class, J.Method) ->
  ProgramLoc ->
  Setup.CrucibleSetupState CJ.JVM
initialCrucibleSetupState cc (cls, method) loc =
  Setup.makeCrucibleSetupState () cc $
    initialDefCrucibleMethodSpecIR
      (cc ^. jccCodebase)
      (J.className cls)
      method
      loc
--------------------------------------------------------------------------------

-- | The default JVM intrinsics extended with the 'MS.GhostValue' intrinsic,
-- which powers ghost state.
intrinsics :: MapF.MapF SymbolRepr (CS.IntrinsicMuxFn Sym)
intrinsics =
  MapF.insert
    (knownSymbol :: SymbolRepr MS.GhostValue)
    CS.IntrinsicMuxFn
    CJ.jvmIntrinsicTypes

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
