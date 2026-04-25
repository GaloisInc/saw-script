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

/-! ## Opaque types (SAWCore `primitive` declarations, no body) -/

/-- SAWCore Prelude `Stream : sort 0 → sort 0`. -/
axiom Stream : Type → Type

/-- SAWCore Prelude `Integer : sort 0`. Mapped to Lean's `Int` at
use sites via `SpecialTreatment`; declared here only so the primitive
appears in one canonical place. -/
axiom Integer : Type

/-! ## Arithmetic primitives -/

axiom subNat : Nat → Nat → Nat
axiom addNat : Nat → Nat → Nat

axiom intSub : Int → Int → Int
axiom intNeg : Int → Int
axiom natToInt : Nat → Int
axiom intToNat : Int → Nat
axiom intLe : Int → Int → Bool

/-! ## Vector primitives -/

/-- SAWCore `gen n a f = [f 0, f 1, …, f (n-1)]`. -/
axiom gen : (n : Nat) → (α : Type) → (Nat → α) → Vec n α

/-- SAWCore `atWithDefault n a d v i` is `v[i]` if `i < n`, else `d`. -/
axiom atWithDefault : (n : Nat) → (α : Type) → α → Vec n α → Nat → α

/-- SAWCore `foldr a b n f z v = f v[0] (f v[1] (... (f v[n-1] z))). -/
axiom foldr : (α β : Type) → (n : Nat) → (α → β → β) → β → Vec n α → β

/-! ## Unsafe / transport primitives -/

/-- SAWCore's `coerce` transports a value across a type equality. -/
axiom coerce : (α β : Type) → @Eq Type α β → α → β

/-- SAWCore's `unsafeAssert` axiom: any equality holds. Universe-
polymorphic in the sort of the equated type, matching SAWCore's
`(a : sort 1) → (x y : a) → Eq a x y`. -/
axiom unsafeAssert.{u} : (α : Sort u) → (x y : α) → @Eq α x y

/-- SAWCore's `error` axiom: produces an inhabitant of any type.
Universe-polymorphic. -/
axiom error.{u} : (α : Sort u) → String → α

end CryptolToLean.SAWCorePrimitives
