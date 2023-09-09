{- |
Module      : SAWScript.Crucible.MIR.Setup.Value
Description : Data types and type family instances for MIR-specific code
License     : BSD3
Maintainer  : Ryan Scott <rscott@galois.com>
Stability   : provisional

The module exists separately from "SAWScript.Crucible.MIR.MethodSpecIR"
primarily to avoid import cycles. You probably want to import
"SAWScript.Crucible.MIR.MethodSpecIR" (which re-exports everything from this
module, plus additional functionality) instead.
-}

{-# Language DataKinds #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}
{-# Language TemplateHaskell #-}
{-# Language TypeFamilies #-}

module SAWScript.Crucible.MIR.Setup.Value
  ( -- * @MIRCrucibleContext@
    MIRCrucibleContext(..)
  , mccRustModule
  , mccBackend
  , mccSimContext
  , mccSymGlobalState
  , mccStaticInitializerMap

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
  ) where

import Control.Lens (makeLenses)
import Data.Parameterized.Classes
import Data.Parameterized.Map (MapF)
import Data.Parameterized.Some
import Data.Text (Text)
import Data.Void (Void)

import Lang.Crucible.Simulator (GlobalVar, RegValue', SimContext, SymGlobalState)
import Lang.Crucible.Types
import Mir.DefId
import Mir.Generator
import Mir.Intrinsics
import qualified Mir.Mir as M

import           SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.Setup.Value as MS

type instance MS.XSetupNull MIR = Void
type instance MS.XSetupGlobal MIR = ()
type instance MS.XSetupStruct MIR = M.Adt
type instance MS.XSetupTuple MIR = ()
-- The 'M.Ty' represents the type of array elements.
type instance MS.XSetupArray MIR = M.Ty
type instance MS.XSetupElem MIR = ()
type instance MS.XSetupField MIR = ()
type instance MS.XSetupCast MIR = Void
type instance MS.XSetupUnion MIR = Void
type instance MS.XSetupGlobalInitializer MIR = ()

type instance MS.XGhostState MIR = Void

type instance MS.TypeName MIR = Text
type instance MS.ExtType MIR = M.Ty

type instance MS.MethodId MIR = DefId
type instance MS.AllocSpec MIR = Some MirAllocSpec
type instance MS.PointsTo MIR = MirPointsTo
type instance MS.ResolvedState MIR = ()

type instance MS.Codebase MIR = CollectionState

data MIRCrucibleContext =
  MIRCrucibleContext
  { _mccRustModule           :: RustModule
  , _mccBackend              :: SomeOnlineBackend
  , _mccSimContext           :: SimContext (SAWCruciblePersonality Sym) Sym MIR
  , _mccSymGlobalState       :: SymGlobalState Sym
  , _mccStaticInitializerMap :: MirStaticInitializerMap
  }

type instance MS.CrucibleContext MIR = MIRCrucibleContext

type instance MS.Pointer' MIR sym = Some (MirPointer sym)

-- | A 'MirStaticInitializerMap' maps the 'GlobalVar's of each top-level static
-- value in a 'Mir.RustModule' to its initializer value (post-Crucible
-- translation). See @Note [Translating MIR statics in SAW]@ in
-- "SAWScript.Crucible.MIR.Builtins" for more details on how this map is
-- created.
type MirStaticInitializerMap = MapF GlobalVar (RegValue' Sym)

-- | Unlike @LLVMPointsTo@ and @JVMPointsTo@, 'MirPointsTo' contains a /list/ of
-- 'MS.SetupValue's on the right-hand side. This is due to how slices are
-- represented in @crucible-mir-comp@, which stores the list of values
-- referenced by the slice. The @mir_points_to@ command, on the other hand,
-- always creates 'MirPointsTo' values with exactly one value in the list (see
-- the @firstPointsToReferent@ function in "SAWScript.Crucible.MIR.Override").
data MirPointsTo = MirPointsTo MS.ConditionMetadata (MS.SetupValue MIR) [MS.SetupValue MIR]
    deriving (Show)

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

makeLenses ''MIRCrucibleContext
makeLenses ''MirAllocSpec
makeLenses ''MirPointer
