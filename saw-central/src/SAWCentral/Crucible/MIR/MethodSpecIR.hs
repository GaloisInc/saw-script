{-# Language DataKinds #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}
{-# Language TemplateHaskell #-}
{-# Language TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

-- | Provides type-checked representations for Rust/MIR function specifications
-- and functions for creating them from ASTs.
module SAWCentral.Crucible.MIR.MethodSpecIR
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
  , MirPointsToTarget(..)

    -- * @MirAllocSpec@
  , MirAllocSpec(..)
  , maConditionMetadata
  , maType
  , maPtrKind
  , maMutbl
  , maMirType
  , maLen

  , mutIso
  , isMut

    -- * @MirPointer@
  , MirPointer(..)
  , mpType
  , mpKind
  , mpMutbl
  , mpMirType
  , mpRef

    -- * @MirPointerKind@
  , MirPointerKind(..)
  , ptrKindToTy
  , tyToPtrKind

    -- * @MIRMethodSpec@
  , MIRMethodSpec

    -- * @MirSetupEnum@
  , MirSetupEnum(..)

    -- * @MirSetupSlice@
  , MirSetupSlice(..)
  , MirSliceInfo(..)

    -- * @MirIndexingKind@
  , MirIndexingMode(..)

    -- * Initial CrucibleSetupMethodSpec
  , initialDefCrucibleMethodSpecIR
  , initialCrucibleSetupState

    -- * Intrinsics
  , intrinsics
  ) where

import Control.Lens (Getter, Iso', Lens', (^.), iso, to)
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.SymbolRepr (SymbolRepr, knownSymbol)
import qualified Data.Text as Text
import qualified Prettyprinter as PP

import Lang.Crucible.FunctionHandle (HandleAllocator)
import Lang.Crucible.Simulator (SimContext(..))
import Lang.Crucible.Simulator.Intrinsics
  (IntrinsicMuxFn(IntrinsicMuxFn), IntrinsicTypes)
import Mir.Generator
import Mir.Intrinsics
import qualified Mir.Mir as M
import What4.ProgramLoc (ProgramLoc)

import           SAWCentral.Crucible.Common
import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import qualified SAWCentral.Crucible.Common.Setup.Type as Setup
import           SAWCentral.Crucible.MIR.Setup.Value
import           SAWCentral.Panic

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
    pretty (MirPointsTo _md ref tar) = PP.parens $
        MS.prettySetupValue ref PP.<+>
          case tar of
            CrucibleMirCompPointsToTarget svs ->
              "->" PP.<+> PP.list (map MS.prettySetupValue svs)
            MirPointsToSingleTarget sv ->
              "->" PP.<+> MS.prettySetupValue sv
            MirPointsToMultiTarget svArr ->
              "->*" PP.<+> MS.prettySetupValue svArr

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

-- | Converts a 'MirPointerKind' to a 'M.Ty' constructor.
ptrKindToTy :: MirPointerKind -> M.Ty -> M.Mutability -> M.Ty
ptrKindToTy MirPointerRef = M.TyRef
ptrKindToTy MirPointerRaw = M.TyRawPtr

-- | Gets the 'MirPointerKind' for a reference or pointer type. Panics if the
-- given 'M.Ty' is not a reference or pointer.
tyToPtrKind :: M.Ty -> MirPointerKind
tyToPtrKind (M.TyRef _ _) = MirPointerRef
tyToPtrKind (M.TyRawPtr _ _) = MirPointerRaw
tyToPtrKind ty = panic "tyToPtrKind"
  ["Type is not a reference or pointer: " <> Text.pack (show ty)]

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
