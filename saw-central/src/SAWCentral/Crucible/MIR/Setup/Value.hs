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
  , MirPointsToTarget(..)

    -- * @MirAllocSpec@
  , MirAllocSpec(..)
  , maConditionMetadata
  , maType
  , maPtrKind
  , maMutbl
  , maMirType
  , maLen

    -- * @MirPointer@
  , MirPointer(..)
  , mpType
  , mpKind
  , mpMutbl
  , mpMirType
  , mpRef

    -- * @MirPointerKind@
  , MirPointerKind(..)

    -- * @MirSetupEnum@
  , MirSetupEnum(..)

    -- * @MirSetupSlice@
  , MirSetupSlice(..)
  , MirSliceInfo(..)

    -- * @MirIndexingMode@
  , MirIndexingMode(..)
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
type instance MS.XSetupElem MIR = MirIndexingMode
type instance MS.XSetupField MIR = ()
-- The 'M.Ty' represents the pointee type after the cast.
-- See Note [Raw pointer casts].
type instance MS.XSetupCast MIR = M.Ty
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

data MirPointsTo = MirPointsTo MS.ConditionMetadata (MS.SetupValue MIR) MirPointsToTarget
    deriving (Show)

-- | Unlike @LLVMPointsTo@ and @JVMPointsTo@, 'MirPointsTo' may have multiple
-- 'MS.SetupValue's on the right-hand side.
data MirPointsToTarget
  -- | The reference points to a contiguous sequence of values, represented by a
  -- list of 'MS.SetupValue's. For slices, there will be multiple values in the
  -- list, while for regular references, there will only be a single value.
  --
  -- This is only used by @crucible-mir-comp@.
  = CrucibleMirCompPointsToTarget [MS.SetupValue MIR]
  -- | The reference points to a single value.
  --
  -- This is created by the @mir_points_to@ command.
  | MirPointsToSingleTarget (MS.SetupValue MIR)
  -- | The reference points to a contiguous sequence of values, represented by a
  -- single 'MS.SetupValue' of array type. The 'MS.SetupValue' argument must
  -- have the 'M.TyArray' MIR type.
  --
  -- This is created by the @mir_points_to_multi@ command.
  | MirPointsToMultiTarget (MS.SetupValue MIR)
  deriving (Show)

data MirAllocSpec tp = MirAllocSpec
    { _maConditionMetadata :: MS.ConditionMetadata
    -- | TypeRepr of the /pointee/ type
    , _maType :: TypeRepr tp
    -- | Which kind of /pointer/
    , _maPtrKind :: MirPointerKind 
    , _maMutbl :: M.Mutability
    -- | MIR Ty of the /pointee/ type
    , _maMirType :: M.Ty
    , _maLen :: Int
    }
  deriving (Show)

instance ShowF MirAllocSpec where

data MirPointer sym tp = MirPointer
    { -- | TypeRepr of the /pointee/ type
      _mpType :: TypeRepr tp
      -- | Which kind of /pointer/
    , _mpKind :: MirPointerKind
    , _mpMutbl :: M.Mutability
      -- | MIR Ty of the /pointee/ type
    , _mpMirType :: M.Ty
    , _mpRef :: MirReferenceMux sym
    }

-- | The kind of a MIR pointer.
data MirPointerKind
  = MirPointerRef -- ^ a reference
  | MirPointerRaw -- ^ a raw pointer
  deriving (Eq, Show)

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

-- | How to do array indexing.
data MirIndexingMode
  -- | Take a MIR array value and return the value of one of its elements.
  = MirIndexIntoVal
  -- | Take a reference/pointer to a MIR array and return a reference/pointer to
  -- one of its elements.
  | MirIndexIntoRef
  -- | Take a reference/pointer to an element within a MIR array and return a
  -- reference/pointer to another element within the same MIR array.
  --
  -- Only used by @crucible-mir-comp@ for now.
  | MirIndexOffsetRef
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

{-
Note [Raw pointer casts]
~~~~~~~~~~~~~~~~~~~~~~~~
Rust and crucible-mir allow casting the pointee type of raw pointers to
arbitrary types, as long as both the old and new pointer types have the same
representation (e.g. the old and new pointee types are both Sized). But when a
pointer is used to actually read from or write to some memory, the pointer's
pointee type must match the actual type inside the memory allocation. In other
words, a pointer to an allocation of type T can be passed around and stored as a
pointer to any other type, as long as it is casted back to *T when it is
actually used.

However, in SAW, this means we need the ability to describe a pointer which
points to an allocation of a different type, because this memory layout may
appear as the precondition or postcondition of a function, even if no Rust code
actually dereferences that pointer without casting it back.

We use mir_cast_raw_ptr/SetupCast to handle this mismatch between the static
pointee type of the pointer and the type of the allocation it is actually
pointing to. Since the purpose of SetupCast is basically to circumvent SAW's
SetupValue type system for raw pointers' pointee types, typeOfSetupValue on a
SetupCast naturally returns TyRawPtr with the post-cast pointee type. But as a
consequence, for raw pointers, the Mir.Ty/TypeShape inside SAW may not always be
correct with respect to the actual type inside the Crucible allocation. This is
tricky to deal with, so here is some analysis about which types are "right" and
"wrong".

Since mir_alloc_raw_ptr returns a SetupVar directly, no cast can happen here,
and the MirAllocSpec created by it will always have the same pointee type as was
actually given to mir_alloc_raw_ptr. If this mir_alloc_raw_ptr is in the
precondition section, then the MirAllocSpec will always have the "right" pointee
type, because the Crucible allocation will be created by SAW according to the
MirAllocSpec. This happens in doAlloc, which returns a MirPointer containing the
Crucible MirReferenceMux, and here the pointee type stored in the MirPointer
will also be the "right" one with respect to the MirReferenceMux, because it is
obtained from the MirAllocSpec.

But if the mir_alloc_raw_ptr is in the postcondition, Crucible is the one that
is creating the allocation, as part of symbolic execution. Then at the end of
execution, SAW matches on it against the type that it thinks it should be (in
matchArg). For instance, if the pointer is the return value, then SAW will match
against the return type of the Rust function from the MIR. But if the function
is returning a casted pointer, this return type will be "wrong" with respect to
the type inside the Crucible reference. matchArg pairs these together in a
MirPointer, and we would like to keep the invariant that the MirPointer's
pointee type is always "right". Therefore, if a cast is involved, we don't want
to look at the "expected" type given to matchArg. The only other place we might
get a type from is the pointee type in the MirAllocSpec, i.e. the type given to
mir_alloc_raw_ptr, so we look at that. But since we are in the postcondition, we
have no guarantee that that type is "right" either.

Fundamentally, pointer casting introduces some level of type unsafety, so we
just have to trust the user that the type they mir_alloc'd is the "right" type
(unless we want to actually inspect the Crucible MirReferenceMux from SAW, which
I'm not sure we want to do, and even then we only get back a Crucible TypeRepr,
not a MIR Ty). If there is no mir_points_to for that pointer, that is the best
we can do, but that's probably fine, since the pointee type is not that
important if the pointee is unspecified. (If the verification result is then
used as an override in a function that does use that pointer, the verification
of that function will fail.) But if there is a mir_points_to, we can cross-check
it with the type of the right hand side of mir_points_to. Since there would be a
Crucible error if the mir_points_to RHS is the wrong type (because the
Mir.readMirRefIO in learnPointsTo wouldn't find any MirReference with that type
in the mux tree), we can assume that if the poststate verification succeeds, the
mir_points_to RHS has the "right" type. Finally, it is possible that the user
still mir_alloc'd a pointer of the "wrong" type, and used mir_cast_raw_ptr when
passing it to mir_points_to. So we must check that mir_points_to does not
contain any casts on the left hand side. Once we do that, we know that the type
passed to mir_alloc is "right".

On the other hand, we cannot in general guarantee that the pointee type of a
pointer in a MIRVal always matches with the Crucible reference in the MIRVal.
For instance, a MIRVal is created when SAW receives the return value of a
function back from Crucible as a RegValue. That is paired with a TypeShape
derived from the declared return type of the Rust function in the MIR. There is
no way of telling from the MIR signature that that type might be "wrong" with
respect to the actual type of the allocation. So if the function returns a
casted pointer, the resulting MIRVal will have mismatched pointee types.

In summary:

- In a MirPointsTo, the pointee type of the left hand side always matches the
  type of the right hand side.

- In a MirAllocSpec, the pointee type always matches the type which will be
  stored in the MirReferenceMux (except in the case of a postcondition
  mir_alloc_raw_ptr with no mir_points_to, in which case we assume that the user
  supplied the right type).

- In a MirPointer, the pointee type always matches the type stored in the
  MirReferenceMux.

- In general, the pointee type of a pointer MIRVal does not necessarily match
  the type stored in the MirReferenceMux.

With these invariants, we can make sure that when we create, read, or write
Crucible references from SAW, the TypeRepr's we pass are always "right".

The only place we create references is the call to Mir.newMirRefIO in doAlloc.
The TypeRepr we pass is obtained from a MirAllocSpec, which always has the
"right" type, so this call is correctly typed.

The only place we read references is the call to Mir.readMirRefIO in
learnPointsTo. The TypeRepr and MirReferenceMux we pass to it are both derived
from the MIRVal returned from calling resolveSetupValueMIR on the left hand side
of a mir_points_to. resolveSetupValueMIR calls resolveSetupVal, which creates a
MIRVal from a MirPointer. Let's say that a data type containing both a pointee
type and a MirReferenceMux is "consistent" if the pointee type matches the type
stored in the MirReferenceMux. Since all MirPointer's are consistent, the MIRVal
resolved from the SetupVar is consistent too. And since there is no SetupCast on
the LHS of any mir_points_to, the MIRVal resolved from the overall LHS
SetupValue is also consistent. Hence the Mir.readMirRefIO call is correctly
typed.

We write to references with Mir.writeMirRefIO in doAlloc and doPointsTo. In
doAlloc, the MirReferenceMux we pass is the one we just got from
Mir.newMirRefIO, and the TypeRepr we pass is the same one we just passed to
Mir.newMirRefIO, so this call is correctly typed. (The CrucibleType type
parameter in writeMirRefIO guarantees that the pointee RegValue we are writing
always matches the TypeRepr we passed.) In doPointsTo, we obtain the TypeRepr
and MirReferenceMux from the MIRVal returned by calling resolveSetupVal on the
left hand side of a mir_points_to. By the same reasoning as above, the MIRVal is
consistent, so the writeMirRefIO call is correctly typed.

All of the above only applies to SAW, not crux-mir-comp, but there's no way of
constructing a SetupCast in crux-mir-comp yet, so we don't have to worry about
this for now...
-}
