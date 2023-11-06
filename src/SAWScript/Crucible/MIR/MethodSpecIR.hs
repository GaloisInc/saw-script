{-# Language DataKinds #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}
{-# Language TemplateHaskell #-}
{-# Language TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

-- | Provides type-checked representations for Rust/MIR function specifications
-- and functions for creating them from ASTs.
module SAWScript.Crucible.MIR.MethodSpecIR
  ( -- * @MIRCrucibleContext@
    MIRCrucibleContext(..)
  , mccRustModule
  , mccBackend
  , mccSimContext
  , mccSymGlobalState
  , mccStaticInitializerMap
  , mccHandleAllocator
  , mccWithBackend
  , mccSym

    -- * @MirStaticInitializerMap@
  , MirStaticInitializerMap

    -- * @MirPointsTo@
  , MirPointsTo(..)

    -- * @MirAllocSpec@
  , MirAllocSpec(..)
  , maType
  , maMutbl
  , maMirType
  , maLen

    -- * @MirPointer@
  , MirPointer(..)
  , mpType
  , mpMutbl
  , mpMirType
  , mpRef

    -- * @MIRMethodSpec@
  , MIRMethodSpec

    -- * @MirSetupSlice@
  , MirSetupSlice(..)

    -- * Initial CrucibleSetupMethodSpec
  , initialDefCrucibleMethodSpecIR
  , initialCrucibleSetupState
  ) where

import Control.Lens (Getter, (^.), to)
import qualified Prettyprinter as PP

import Lang.Crucible.FunctionHandle (HandleAllocator)
import Lang.Crucible.Simulator (SimContext(..))
import Mir.Generator
import Mir.Intrinsics
import qualified Mir.Mir as M
import What4.ProgramLoc (ProgramLoc)

import           SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Setup.Type as Setup
import           SAWScript.Crucible.MIR.Setup.Value

mccHandleAllocator :: Getter MIRCrucibleContext HandleAllocator
mccHandleAllocator = mccSimContext . to simHandleAllocator

mccWithBackend ::
  MIRCrucibleContext ->
  (forall solver. OnlineSolver solver => Backend solver -> a) ->
  a
mccWithBackend cc k =
  case _mccBackend cc of SomeOnlineBackend bak -> k bak

mccSym :: Getter MIRCrucibleContext Sym
mccSym = to (\mcc -> mccWithBackend mcc backendGetSym)

instance PP.Pretty MirPointsTo where
    pretty (MirPointsTo _md ref sv) = PP.parens $
        MS.ppSetupValue ref PP.<+> "->" PP.<+> PP.list (map MS.ppSetupValue sv)

type MIRMethodSpec = MS.CrucibleMethodSpecIR MIR

initialDefCrucibleMethodSpecIR ::
  CollectionState ->
  M.Fn ->
  ProgramLoc ->
  MS.CrucibleMethodSpecIR MIR
initialDefCrucibleMethodSpecIR rm fn loc =
  let fname = fn ^. M.fname
      fsig = fn ^. M.fsig
      argTys = fsig ^. M.fsarg_tys
      retTy = case fsig ^. M.fsreturn_ty of
                M.TyTuple [] -> Nothing
                ty -> Just ty in
  MS.makeCrucibleMethodSpecIR fname argTys retTy loc rm

initialCrucibleSetupState ::
  MIRCrucibleContext ->
  M.Fn ->
  ProgramLoc ->
  Setup.CrucibleSetupState MIR
initialCrucibleSetupState cc fn loc =
  Setup.makeCrucibleSetupState () cc $
    initialDefCrucibleMethodSpecIR
      (cc ^. mccRustModule ^. rmCS)
      fn
      loc
