{-# Language DataKinds #-}
{-# Language TypeFamilies #-}
{-# Language OverloadedStrings #-}

module Mir.Compositional.MethodSpec
where

import Data.Parameterized.Pair
import Data.Parameterized.Some
import Data.Text (Text)
import qualified Prettyprinter as PP

import Lang.Crucible.Types

import qualified SAWScript.Crucible.Common.MethodSpec as MS
import qualified SAWScript.Crucible.Common.Override as MS

import Mir.DefId
import Mir.Generator
import Mir.Intrinsics
import qualified Mir.Mir as M


type instance MS.HasSetupNull MIR = 'False
type instance MS.HasSetupGlobal MIR = 'False
type instance MS.HasSetupStruct MIR = 'True
type instance MS.HasSetupArray MIR = 'True
type instance MS.HasSetupElem MIR = 'True
type instance MS.HasSetupField MIR = 'True
type instance MS.HasSetupGlobalInitializer MIR = 'False

type instance MS.HasGhostState MIR = 'False

type instance MS.TypeName MIR = Text
type instance MS.ExtType MIR = M.Ty

type instance MS.MethodId MIR = DefId
type instance MS.AllocSpec MIR = (Some TypeRepr, M.Mutability, M.Ty)
type instance MS.PointsTo MIR = MirPointsTo

type instance MS.Codebase MIR = CollectionState

type instance MS.CrucibleContext MIR = ()

type instance MS.Pointer' MIR sym = Pair TypeRepr (MirReferenceMux sym)


data MirPointsTo = MirPointsTo MS.AllocIndex (MS.SetupValue MIR)
    deriving (Show)

instance PP.Pretty MirPointsTo where
    pretty (MirPointsTo alloc sv) = PP.parens $
        PP.pretty (show alloc) PP.<+> "->" PP.<+> MS.ppSetupValue sv

type MIRMethodSpec = MS.CrucibleMethodSpecIR MIR
