{- |
Module      : SAWCentral.Crucible.MIR.Setup.Value
Description : Data types and type family instances for MIR-specific code
License     : BSD3
Maintainer  : Ryan Scott <rscott@galois.com>
Stability   : provisional

The module exists separately from "SAWCentral.Crucible.MIR.MethodSpecIR"
primarily to avoid import cycles. You probably want to import
"SAWCentral.Crucible.MIR.MethodSpecIR" (which re-exports everything from this
module, plus additional functionality) instead.
-}

{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}
{-# Language StandaloneDeriving #-}
{-# Language TemplateHaskell #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SAWCentral.Crucible.MIR.Setup.Value
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
  , maConditionMetadata
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

    -- * @MirSetupEnum@
  , MirSetupEnum(..)

    -- * @MirSetupSlice@
  , MirSetupSlice(..)
  , MirSliceInfo(..)
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

import           SAWCentral.Crucible.Common
import qualified SAWCentral.Crucible.Common.Setup.Value as MS

type instance MS.XSetupNull MIR = Void
type instance MS.XSetupGlobal MIR = ()
type instance MS.XSetupStruct MIR = M.Adt
type instance MS.XSetupEnum MIR = MirSetupEnum
type instance MS.XSetupTuple MIR = ()
type instance MS.XSetupSlice MIR = MirSetupSlice
-- The 'M.Ty' represents the type of array elements.
type instance MS.XSetupArray MIR = M.Ty
type instance MS.XSetupElem MIR = ()
type instance MS.XSetupField MIR = ()
type instance MS.XSetupCast MIR = Void
type instance MS.XSetupUnion MIR = Void
type instance MS.XSetupGlobalInitializer MIR = ()
type instance MS.XSetupMux MIR = ()

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
-- "SAWCentral.Crucible.MIR.Builtins" for more details on how this map is
-- created.
type MirStaticInitializerMap = MapF GlobalVar (RegValue' Sym)

-- | Unlike @LLVMPointsTo@ and @JVMPointsTo@, 'MirPointsTo' contains a /list/ of
-- 'MS.SetupValue's on the right-hand side. This is due to how slices are
-- represented in @crucible-mir-comp@, which stores the list of values
-- referenced by the slice. The @mir_points_to@ command, on the other hand,
-- always creates 'MirPointsTo' values with exactly one value in the list (see
-- the @firstPointsToReferent@ function in "SAWCentral.Crucible.MIR.Override").
data MirPointsTo = MirPointsTo MS.ConditionMetadata (MS.SetupValue MIR) [MS.SetupValue MIR]
    deriving (Show)

data MirAllocSpec tp = MirAllocSpec
    { _maConditionMetadata :: MS.ConditionMetadata
    , _maType :: TypeRepr tp
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
    , _mpRef :: MirReferenceMux sym
    }

-- | A enum-related MIR 'SetupValue'.
data MirSetupEnum where
  -- | A specific variant of an enum.
  MirSetupEnumVariant ::
       M.Adt
       -- ^ The enum type.
    -> M.Variant
       -- ^ The variant to use.
    -> Int
       -- ^ The index of the variant within the list of all the enum's variants.
       -- In most circumstances, this index will be the same as the discriminant
       -- value, but the index can be different if a variant uses an explicit
       -- value. For instance, in this example:
       --
       -- @
       -- enum A {
       --     A0,
       --     A1,
       -- }
       --
       -- enum B {
       --     B0 = 42,
       --     B1,
       -- }
       -- @
       --
       -- The indexes for @A0@ and @B0@ are both @0@, and the indexes for @A1@
       -- and @B1@ are both @1@. The discriminant values are different, however.
       -- The discriminants for @A0@ and @A1@ are @0@ and @1@, respectively,
       -- while the discriminants for @B0@ and @B1@ are @42@ and @43@,
       -- respectively.
       --
       -- Note that the index is accessible within the 'M.Variant' argument, but
       -- retrieving the information is somewhat involved. (See the
       -- implementation of @mir_enum_value@.) For this reason, we store this
       -- information separately in 'MirSetupEnumVariant' to make it easier to
       -- look up later.
    -> [MS.SetupValue MIR]
       -- ^ The values of the variant's fields.
    -> MirSetupEnum

  -- | A symbolic enum value, where the 'M.Adt' represents the enum type.
  -- This is only used in the implementation of @mir_fresh_expanded_value@.
  -- See @Note [Symbolic enums]@ for a more detailed explanation.
  --
  -- Note that @repr(transparent)@ enums never use 'MirSetupEnumSymbolic'.
  -- Instead, they are represented as a 'MirSetupEnumVariant' where the
  -- underlying variant field is symbolic. This makes it simpler to ensure that
  -- resolving a @repr(transparent@ enum value will yield a 'MIRVal' whose
  -- 'TypeShape' is 'TransparentShape'.
  MirSetupEnumSymbolic ::
       M.Adt
       -- ^ The enum type.
    -> MS.SetupValue MIR
       -- ^ The symbolic discriminant value.
    -> [[MS.SetupValue MIR]]
       -- ^ The symbolic values that are used for the fields in each variant.
       -- For instance, if one created a symbolic value of this type:
       --
       -- @
       -- enum E {
       --     E1(u16),
       --     E2(u32, u32),
       -- @
       --
       -- Then the list of fields would be @[[x], [y, z]]@, where @x: u16@
       -- are the fields of @E1@, and @y: u32@ and @z: u32@ are the fields of
       -- @E2@.
    -> MirSetupEnum
  deriving Show

-- | A slice-related MIR 'SetupValue'. This is used to power the @mir_slice_*@
-- and @mir_str_slice_*@ family of SAWScript functions.
data MirSetupSlice
  = MirSetupSliceRaw (MS.SetupValue MIR) (MS.SetupValue MIR)
    -- ^ A \"raw\" slice constructed directly from a pointer and a length.
    -- Currently, this is only used by @crucible-mir-comp@. SAWScript offers no
    -- way to use this, although we may consider doing so in the future.
  | MirSetupSlice MirSliceInfo (MS.SetupValue MIR)
    -- ^ A slice of a reference to a contiguous sequence 'SetupValue'.
  | MirSetupSliceRange MirSliceInfo (MS.SetupValue MIR) Int Int
    -- ^ A slice of a reference to a contiguous sequence 'SetupValue', where the
    -- slice only covers the range specified by the given start and end values
    -- (the first and second 'Int', respectively). Currently, this only supports
    -- concrete ranges.
  deriving Show

-- | Are we dealing with an array slice (@[T]@) or a string slice (@str@)?
data MirSliceInfo
  = -- | @[T]@ (for some type @T@)
    MirArraySlice
  | -- | @str@
    MirStrSlice
  deriving (Eq, Show)

makeLenses ''MIRCrucibleContext
makeLenses ''MirAllocSpec
makeLenses ''MirPointer

{-
Note [Symbolic enums]
~~~~~~~~~~~~~~~~~~~~~
Creating a symbolic MIR enum value is not quite as straightforward as creating
symbolic versions of other compound types, mostly due to the atypical Crucible
representation that enums use. To recap, if we have an enum like this:

  enum E {
    E1(u16),
    E2(u32, u32),
  }

Then this will be implemented using (roughly) the following Crucible `Type`
under the hood:

  (BVType 64, VariantType [StructType [BVType 16], StructType [BVType 32, BVType 32]])

Where:

* The `BVType 64` is a /discriminant/, whose value indicates which variant is
  in use. For instance, a discriminant value of `0` indicates that the `E1`
  variant is in use, and a discriminant value of `1` indicates that the `E2`
  variant is in use.
* The `VariantType ...` indicates that there are two variants in this enum,
  where each variant is represented as a struct with the corresponding fields
  in that variant.

At simulation time, VariantTypes are represented as a sequence of
VariantBranches, where a VariantBranch is (roughly) a pair of:

* A (possibly symbolic) predicate indicating if that variant is being used, and
* A payload representing the fields of the enum. If the predicate does not
  hold, then the payload will likely be symbolic, since it does not matter what
  the payload value is in that case.

OK, recap over. Let's get back to the original question: how do we make a
symbolic value of this type? A naïve first attempt is to generate fresh
symbolic values for everything. That is, a symbolic discriminant, as well as a
symbolic predicate and payload for each VariantBranch. While tempting, this
approach won't work. To see why, consider what happens when one pattern matches
on a symbolic enum value. For example, the `match` expression in this function:

  fn foo(x: E) -> u32 {
      match x {
          E::E1(a) => bar(y),
          E::E2(b, c) => baz(b, c),
      }
  }

Would turn into the (roughly) following MIR:

  fn foo(x : E) -> u32 {
      start_block: {
          discr = Discriminant(x, isize);
          switchint discr :isize [0, 1] -> [e1_block, e2_block, fallthrough_block]
      }
      e1_block: {
          ... call bar() ...
      }
      e2_block: {
          ... call baz() ...
      }
      fallthrough_block: {
          unreachable;
      }
      ...
  }

Here, the `switchint discr` statement will check the value of `discr` (the
discriminant), and if it equals `0`, go to `e1_block`; if it equals `1`, go to
`e2_block`; and if it equals something else, go to `fallthrough_block`. In
normal circumstances, `discr` should only ever be equal to `0` or `1`, which
implies that `fallthrough_block` should never be accessible (as indicated by
its `unreachable` instruction).

Now consider what would happen if the discriminant were an unconstrained,
symbolic value. While a symbolic discriminant could be equal to `0` or `1`, it
could also be equal to any other value! This would spell disaster if Crucible
tried to perform a symbolic branch on, say, `discr == 2`, since that would
cause execution to reach `fallthrough_block` and crash. We want a symbolic
discriminant, but we don't want it to be /that/ symbolic!

For this reason, after we create a symbolic discriminant value, we also add a
Crucible assumption that the discriminant must be equal to one of the possible
enum variants' discriminants. In the example above, this means that we would
assume assume the following:

  (discr == 0) \/ (discr == 1)

This way, symbolic execution will never reach `fallthrough_block`. This
Crucible assumption is created in
SAWCentral.Crucible.MIR.Builtins.constructExpandedSetupValue.goEnum`.

Similarly, we cannot make the VariantBranch predicates completely symbolic, as
whether a predicate holds or not depends on the value of the discriminant. For
this reason, we do not create fresh variables for each predicate, but instead
make each predicate the result of checking the discriminant against particular
values. For instance, the predicate for the `E1` VariantBranch is defined to be
`discr == 0`, and the predicate for the `E2` VariantBranch is defined to be
`discr == 1`. These predicates are defined in
`SAWCentral.Crucible.MIR.ResolveSetupValue.resolveSetupValue`, along with the
fields in the associated payloads.

Lastly, there are the payloads (i.e., the fields of each variant) in each
VariantBranch. These are created as completely symbolic values—the trick is to
only access the fields when the corresponding predicate holds. For example,
`SAWCentral.Crucible.MIR.Override.matchArg` (in the `MirSetupEnumSymbolic` case)
must be able to match two possibly symbolic enum values together, but it must
be careful to only match the fields in a variant if that VariantBranch's
predicate holds.

To make this a bit more specific, suppose we have two symbolic enum values
`enumA` and `enumA`, where:

* `enumA` has the discriminant value `discrA`, and
  `enumB` has the discriminant value `discrB`.
* `enumA` has the VariantBranches [(e1_pred_a, [e1_fld1_a]), (e2_pred_a, [e2_fld1_a, e2_fld2_a])], and
  `enumB` has the VariantBranches [(e1_pred_b, [e1_fld1_b]), (e2_pred_b, [e2_fld1_b, e2_fld2_b])].

We only want to match `e1_fld1_a` against `e1_fld1_b` if both enums are using
the `E1` variant, that is, if `e1_pred_a` and `e_pred_b` hold. To this end, the
`matchArg` function checks this by generating (roughly) the following
assertion:

  (discrA == discrB) /\
  (e1_pred_a ==> (e1_fld1_a == e1_fld1_b))

(Note that instead of `e1_pred_a ==> ...`, we could have alternatively used
`e1_pred_b ==> ...`, `(discrA == 0) ==> ...`, or `(discrB == 0) ==> ...`. All
formulations are equivalent.)

Phew! Enums are surprisingly tricky.
-}
