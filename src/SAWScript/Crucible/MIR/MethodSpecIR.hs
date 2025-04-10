{-# Language DataKinds #-}
{-# Language LambdaCase #-}
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
  , mccIntrinsicTypes
  , mccWithBackend
  , mccSym

    -- * @MirStaticInitializerMap@
  , MirStaticInitializerMap

    -- * @MirPointsTo@
  , MirPointsTo(..)

    -- * @MirAllocSpec@
  , MirAllocSpec(..)
  , maConditionMetadata
  , maType
  , maMutbl
  , maMirType
  , maLen

  , mutIso
  , isMut

    -- * @MirPointer@
  , MirPointer(..)
  , mpType
  , mpMutbl
  , mpMirType
  , mpRef

    -- * @MIRMethodSpec@
  , MIRMethodSpec

    -- * @MirSetupEnum@
  , MirSetupEnum(..)

    -- * @MirSetupSlice@
  , MirSetupSlice(..)
  , MirSliceInfo(..)

    -- * Initial CrucibleSetupMethodSpec
  , initialDefCrucibleMethodSpecIR
  , initialCrucibleSetupState

    -- * Intrinsics
  , intrinsics
  ) where

import Control.Lens (Getter, Iso', Lens', (^.), iso, to)
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.SymbolRepr (SymbolRepr, knownSymbol)
import qualified Prettyprinter as PP

import Lang.Crucible.FunctionHandle (HandleAllocator)
import Lang.Crucible.Simulator (SimContext(..))
import Lang.Crucible.Simulator.Intrinsics
  (IntrinsicMuxFn(IntrinsicMuxFn), IntrinsicTypes)
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

mccIntrinsicTypes :: Getter MIRCrucibleContext (IntrinsicTypes Sym)
mccIntrinsicTypes = mccSimContext . to ctxIntrinsicTypes

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

mutIso :: Iso' M.Mutability Bool
mutIso =
  iso
    (\case
      M.Mut -> True
      M.Immut -> False)
    (\case
      True -> M.Mut
      False -> M.Immut)

isMut :: Lens' (MirAllocSpec tp) Bool
isMut = maMutbl . mutIso

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

-- | The default MIR intrinsics extended with the 'MS.GhostValue' intrinsic,
-- which powers ghost state.
intrinsics :: MapF.MapF SymbolRepr (IntrinsicMuxFn Sym)
intrinsics =
  MapF.insert
    (knownSymbol :: SymbolRepr MS.GhostValue)
    IntrinsicMuxFn
    mirIntrinsicTypes
