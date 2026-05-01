/-
`CryptolToLean.SAWCorePrimitives` — axiomatic + inductive stand-ins
for the SAWCore primitives that survive `scNormalize`.

The specialization approach (see `doc/2026-04-23_stage3-translator-
sketch.md`) normalizes each user term before translation. Everything
that survives is either

- a SAWCore axiom / primitive (no body), or
- a SAWCore inductive / its auto-generated recursor, or
- a SAWCore constructor,

and this file enumerates a realisation for each one the translator
emits a reference to.

**Soundness discipline.** Every realisation must be semantically
equivalent to the SAWCore source it replaces. If in doubt, prove the
equivalence. See `doc/2026-04-22_soundness.md`.

Scope: seeded for the Stage 4 implRev4 driver. Extend as further
Cryptol demos surface additional primitives.
-/

import CryptolToLean.SAWCoreVectors

namespace CryptolToLean.SAWCorePrimitives

open CryptolToLean.SAWCoreVectors (Vec)

/-! ## Inductives -/

/-- SAWCore Prelude `Either a b` — standard coproduct. Matches
Lean's standard sum but defined here so the SAWCore translator can
emit `@CryptolToLean.SAWCorePrimitives.Either.Left …` without
importing Lean's `Sum`. -/
inductive Either (α β : Type) : Type where
  | Left  : α → Either α β
  | Right : β → Either α β

/-- Cryptol Prelude `Num` (from `Cryptol.sawcore`). The marker used
throughout Cryptol's numeric-kind machinery: a finite length (via
`TCNum`) or an infinite stream marker (`TCInf`).

SAWCore's `Nat` is mapped to Lean's native `Nat` at the
'SpecialTreatment' level (with `NatPos`/`Bit0`/`Bit1`/`One`/`Zero`
collapsed to numeric literals via `UseMacro`), so `TCNum` takes a
Lean `Nat` here. If a future user term exercises SAWCore's
`Nat#rec` with a non-Lean-matching argument order we'll need to
revisit; for now specialization reduces those eliminations away
before the translator sees them. -/
inductive Num : Type where
  | TCNum : Nat → Num
  | TCInf : Num

/-! ## Nat constructor wrappers

SAWCore's `Nat` / `Pos` constructors (`Zero`, `NatPos`, `One`,
`Bit0`, `Bit1`, `Succ`) are mapped to Lean's native `Nat` via
`SpecialTreatment`. When a constructor appears fully applied to a
concrete argument the translator collapses it to a `NatLit`; when
it appears under-applied or applied to a symbolic argument it
falls through to the wrappers below. -/

@[reducible] def bit0_macro (n : Nat) : Nat := 2 * n
@[reducible] def bit1_macro (n : Nat) : Nat := 2 * n + 1

/-- SAWCore Prelude `Stream a` — infinite sequences of `a`. The
single constructor `MkStream : (Nat → a) → Stream a` packages an
indexed view of the stream. -/
inductive Stream (α : Type) : Type where
  | MkStream : (Nat → α) → Stream α

/-- SAWCore Prelude `EmptyType : sort 0` — the "end of record"
marker. Has one constructor `Empty`; Cryptol's records are encoded
as right-nested `RecordType` chains ending in `EmptyType` / `Empty`.
-/
inductive EmptyType : Type where
  | Empty : EmptyType

/-- SAWCore Prelude `RecordType` — a one-field record builder. Paired
with `RecordValue` as the single constructor. Cryptol uses nested
`RecordType` for multi-field records. -/
inductive RecordType (s : String) (α β : Type) : Type where
  | RecordValue : α → β → RecordType s α β

/-! ## Opaque types (SAWCore `primitive` declarations, no body) -/

/-- SAWCore Prelude `Integer : sort 0`. Mapped to Lean's `Int` at
use sites via `SpecialTreatment`; declared here only so the primitive
appears in one canonical place. -/
axiom Integer : Type

/-! ## Arithmetic primitives

These are declared as reducible wrappers over Lean's native
arithmetic rather than opaque axioms. Definitional equality of
arithmetic is needed for type-checking vector sizes (e.g.
Cryptol's `[0..10]` has length `addNat 1 (subNat 10 0)` which Lean
must recognise as `11` to match a `Vec 11` annotation).

SAWCore's `subNat` saturates at zero (`subNat n m = max 0 (n - m)`);
Lean's `Nat.sub` has the same truncated-subtraction semantics. -/

@[reducible] def addNat : Nat → Nat → Nat := Nat.add
@[reducible] def subNat : Nat → Nat → Nat := Nat.sub

-- Comparison wrappers — reducible aliases over Lean's native Nat
-- comparisons. These are only sound because we've already
-- committed to SAW Nat ≡ Lean Nat at the value level.
@[reducible] def equalNat : Nat → Nat → Bool := fun a b => decide (a = b)
@[reducible] def ltNat    : Nat → Nat → Bool := fun a b => decide (a < b)
@[reducible] def leNat    : Nat → Nat → Bool := fun a b => decide (a ≤ b)

axiom intAdd : Int → Int → Int
axiom intSub : Int → Int → Int
axiom intMul : Int → Int → Int
axiom intDiv : Int → Int → Int
axiom intMod : Int → Int → Int
axiom intNeg : Int → Int
axiom intEq : Int → Int → Bool
axiom intLe : Int → Int → Bool
axiom intLt : Int → Int → Bool
axiom natToInt : Nat → Int
axiom intToNat : Int → Nat

/-! ## Bitvector primitives

SAW models bitvectors as `Vec n Bool` (`bitvector n := Vec n
Bool`). The ops below take that representation. They are declared
as opaque axioms rather than reducible aliases because:

  - SAW's semantics are spelled out at value level
    (`Prelude.sawcore` lines 1760-2116) and don't always agree with
    Lean's native `BitVec` ops on edge cases (signed div/rem
    behaviour around zero divisors, `Succ n` vs raw `n` for signed
    ops, etc.).
  - Treating them as axioms means generated Lean elaborates with
    the right /shape/ but doesn't reduce; downstream proofs of
    Cryptol properties have to use the SAW-side semantics, which is
    the soundness boundary the `error`/`unsafeAssert`/`coerce`
    family already establishes.

If a future arc binds these to `Lean.BitVec` operations with proven
coherence theorems, this section can be replaced with reducible
defs. See `doc/2026-05-01_status-and-next-steps.md` Arc 3.

The non-primitive bv ops (`bvNot`, `bvAnd`, `bvOr`, `bvXor`,
`bvEq`) are SAWCore Prelude /defs/ rather than primitives — their
bodies use `map` / `bvZipWith` / `vecEq` over individual `Bool`
ops. We keep them opaque via `leanOpaqueBuiltins` (in
`SAWCentral.Prover.Exporter`) so normalization doesn't expose the
inner machinery, then provide a top-level axiom here. -/

axiom bvNat : (n : Nat) → Nat → Vec n Bool
axiom bvToNat : (n : Nat) → Vec n Bool → Nat
axiom bvToInt : (n : Nat) → Vec n Bool → Int
axiom intToBv : (n : Nat) → Int → Vec n Bool
axiom sbvToInt : (n : Nat) → Vec n Bool → Int

axiom bvAdd : (n : Nat) → Vec n Bool → Vec n Bool → Vec n Bool
axiom bvSub : (n : Nat) → Vec n Bool → Vec n Bool → Vec n Bool
axiom bvMul : (n : Nat) → Vec n Bool → Vec n Bool → Vec n Bool
axiom bvNeg : (n : Nat) → Vec n Bool → Vec n Bool
axiom bvUDiv : (n : Nat) → Vec n Bool → Vec n Bool → Vec n Bool
axiom bvURem : (n : Nat) → Vec n Bool → Vec n Bool → Vec n Bool

-- Signed div/rem are SAW-typed at @Vec (Succ n) Bool@ to forbid
-- zero-width vectors. We mirror that.
axiom bvSDiv : (n : Nat) → Vec (n + 1) Bool → Vec (n + 1) Bool → Vec (n + 1) Bool
axiom bvSRem : (n : Nat) → Vec (n + 1) Bool → Vec (n + 1) Bool → Vec (n + 1) Bool

axiom bvShl : (w : Nat) → Vec w Bool → Nat → Vec w Bool
axiom bvShr : (w : Nat) → Vec w Bool → Nat → Vec w Bool
axiom bvSShr : (w : Nat) → Vec (w + 1) Bool → Nat → Vec (w + 1) Bool

axiom bvNot : (n : Nat) → Vec n Bool → Vec n Bool
axiom bvAnd : (n : Nat) → Vec n Bool → Vec n Bool → Vec n Bool
axiom bvOr  : (n : Nat) → Vec n Bool → Vec n Bool → Vec n Bool
axiom bvXor : (n : Nat) → Vec n Bool → Vec n Bool → Vec n Bool

axiom bvEq  : (n : Nat) → Vec n Bool → Vec n Bool → Bool
axiom bvult : (n : Nat) → Vec n Bool → Vec n Bool → Bool
axiom bvule : (n : Nat) → Vec n Bool → Vec n Bool → Bool
axiom bvugt : (n : Nat) → Vec n Bool → Vec n Bool → Bool
axiom bvuge : (n : Nat) → Vec n Bool → Vec n Bool → Bool
axiom bvslt : (n : Nat) → Vec n Bool → Vec n Bool → Bool
axiom bvsle : (n : Nat) → Vec n Bool → Vec n Bool → Bool
axiom bvsgt : (n : Nat) → Vec n Bool → Vec n Bool → Bool
axiom bvsge : (n : Nat) → Vec n Bool → Vec n Bool → Bool

axiom bvUExt : (m n : Nat) → Vec n Bool → Vec (m + n) Bool
axiom bvSExt : (m n : Nat) → Vec (n + 1) Bool → Vec (m + (n + 1)) Bool

axiom bvPopcount : (n : Nat) → Vec n Bool → Vec n Bool
axiom bvCountLeadingZeros : (n : Nat) → Vec n Bool → Vec n Bool
axiom bvCountTrailingZeros : (n : Nat) → Vec n Bool → Vec n Bool
axiom bvLg2 : (n : Nat) → Vec n Bool → Vec n Bool

/-! ## Vector primitives -/

/-- SAWCore `gen n a f = [f 0, f 1, …, f (n-1)]`. -/
axiom gen : (n : Nat) → (α : Type) → (Nat → α) → Vec n α

/-- SAWCore `shiftL n α z v i` — shift @v@ left by @i@ positions,
filling with @z@. Generic over the element type; the bitvector
shift `bvShl` is the @α = Bool@ specialization. -/
axiom shiftL : (n : Nat) → (α : Type) → α → Vec n α → Nat → Vec n α

/-- SAWCore `shiftR n α z v i` — shift right, filling with @z@. -/
axiom shiftR : (n : Nat) → (α : Type) → α → Vec n α → Nat → Vec n α

/-- SAWCore `atWithDefault n a d v i` is `v[i]` if `i < n`, else `d`. -/
axiom atWithDefault : (n : Nat) → (α : Type) → α → Vec n α → Nat → α

/-- SAWCore `foldr a b n f z v = f v[0] (f v[1] (... (f v[n-1] z))). -/
axiom foldr : (α β : Type) → (n : Nat) → (α → β → β) → β → Vec n α → β

/-- SAWCore `foldl a b n f z v = f (... (f (f z v[0]) v[1])) v[n-1]`. -/
axiom foldl : (α β : Type) → (n : Nat) → (β → α → β) → β → Vec n α → β

/-! ## Unsafe / transport primitives -/

/-- SAWCore's `coerce` transports a value across a type equality. -/
axiom coerce : (α β : Type) → @Eq Type α β → α → β

/-- SAWCore's `unsafeAssert` axiom: any equality holds. Universe-
polymorphic in the sort of the equated type, matching SAWCore's
`(a : sort 1) → (x y : a) → Eq a x y`. -/
axiom unsafeAssert.{u} : (α : Sort u) → (x y : α) → @Eq α x y

/-- SAWCore's `error` axiom: produces an inhabitant of any type.
SAW declares `primitive error : (a : isort 1) → String → a` — i.e.
polymorphic over `Type`-sized types, with an "inhabited" flag that's
advisory. We use `Sort (u+1)` rather than `Sort u` here for a
critical soundness reason: `Sort 0 = Prop`, so a `Sort u`-polymorphic
`error` would let a user importing this module write `exact error
False ""` and produce a proof of `False` from nothing. SAW's
`isort 1` forbids this by construction. `Sort (u+1)` admits
`Type, Type 1, Type 2, …` — i.e. every non-`Prop` sort — which is
everything the translator actually needs (Cryptol terms call
`error` at value-level types like `Vec 8 Bool` or `Int`, and at
higher-sort types like `(α : Type) → Stream α → Stream α` when a
recursor branch over a polymorphic stream is "unreachable"). -/
axiom error.{u} : (α : Sort (u+1)) → String → α

end CryptolToLean.SAWCorePrimitives
