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
  , mccHandleAllocator
  , mccWithBackend
  , mccSym

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

    -- * Initial CrucibleSetupMethodSpec
  , initialDefCrucibleMethodSpecIR
  , initialCrucibleSetupState
  ) where

import Control.Lens (Getter, (^.), makeLenses, to)
import Data.Parameterized.Classes
import Data.Parameterized.Some
import Data.Text (Text)
import qualified Prettyprinter as PP

import Lang.Crucible.FunctionHandle (HandleAllocator)
import Lang.Crucible.Types
import Mir.DefId
import Mir.Generator
import Mir.Intrinsics
import qualified Mir.Mir as M
import What4.ProgramLoc (ProgramLoc)

import           SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Override as MS
import qualified SAWScript.Crucible.Common.Setup.Type as Setup

type instance MS.HasSetupNull MIR = 'False
type instance MS.HasSetupGlobal MIR = 'False
type instance MS.HasSetupStruct MIR = 'True
type instance MS.HasSetupArray MIR = 'True
type instance MS.HasSetupElem MIR = 'True
type instance MS.HasSetupField MIR = 'True
type instance MS.HasSetupCast MIR = 'False
type instance MS.HasSetupUnion MIR = 'False
type instance MS.HasSetupGlobalInitializer MIR = 'False

type instance MS.HasGhostState MIR = 'False

type instance MS.TypeName MIR = Text
type instance MS.ExtType MIR = M.Ty

type instance MS.MethodId MIR = DefId
type instance MS.AllocSpec MIR = Some MirAllocSpec
type instance MS.PointsTo MIR = MirPointsTo
type instance MS.ResolvedState MIR = ()
type instance MS.CastType MIR = ()

type instance MS.Codebase MIR = CollectionState

data MIRCrucibleContext =
  MIRCrucibleContext
  { _mccRustModule      :: RustModule
  , _mccBackend         :: SomeOnlineBackend
  , _mccHandleAllocator :: HandleAllocator
  }

type instance MS.CrucibleContext MIR = MIRCrucibleContext

mccWithBackend ::
  MIRCrucibleContext ->
  (forall solver. OnlineSolver solver => Backend solver -> a) ->
  a
mccWithBackend cc k =
  case _mccBackend cc of SomeOnlineBackend bak -> k bak

mccSym :: Getter MIRCrucibleContext Sym
mccSym = to (\mcc -> mccWithBackend mcc backendGetSym)

type instance MS.Pointer' MIR sym = Some (MirPointer sym)

-- | Unlike @LLVMPointsTo@ and @JVMPointsTo@, 'MirPointsTo' contains a /list/ of
-- 'MS.SetupValue's on the right-hand side. This is due to how slices are
-- represented in @crucible-mir-comp@, which stores the list of values
-- referenced by the slice. The @mir_points_to@ command, on the other hand,
-- always creates 'MirPointsTo' values with exactly one value in the list (see
-- the @firstPointsToReferent@ function in "SAWScript.Crucible.MIR.Override").
data MirPointsTo = MirPointsTo MS.ConditionMetadata MS.AllocIndex [MS.SetupValue MIR]
    deriving (Show)

instance PP.Pretty MirPointsTo where
    pretty (MirPointsTo _md alloc sv) = PP.parens $
        PP.pretty (show alloc) PP.<+> "->" PP.<+> PP.list (map MS.ppSetupValue sv)

data MirAllocSpec tp = MirAllocSpec
    { _maType :: TypeRepr tp
    , _maMutbl :: M.Mutability
    , _maMirType :: M.Ty
    , _maLen :: Int
    }
  deriving (Show)

instance ShowF MirAllocSpec where

data MirPointer sym tp = MirPointer
    { _mpType :: TypeRepr tp
    , _mpMutbl :: M.Mutability
    , _mpMirType :: M.Ty
    , _mpRef :: MirReferenceMux sym tp
    }

type MIRMethodSpec = MS.CrucibleMethodSpecIR MIR

makeLenses ''MIRCrucibleContext
makeLenses ''MirAllocSpec
makeLenses ''MirPointer

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
