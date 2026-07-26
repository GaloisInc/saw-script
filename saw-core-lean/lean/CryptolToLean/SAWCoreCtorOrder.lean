/-
`CryptolToLean.SAWCoreCtorOrder` — the emission-time constructor-order
check for directly-emitted SAWCore recursors.

The saw-core-lean backend emits `@Foo.rec` with SAWCore's positional
argument order (motive, case_1 … case_k, indices, scrutinee), where
the case order is SAWCore's declared constructor order. That is sound
only while the Lean inductive realizing `Foo` declares the same
constructors in the same order. Both sides can drift silently — a
reordered inductive in this support library, or a reordered datatype
declaration in the SAWCore/Cryptol prelude — and for same-payload
constructors the drift TYPECHECKS while swapping every case handler.

`saw_ctor_order` closes that hole: the backend emits one assertion per
datatype whose recursor it emits, generated from SAWCore's declared
constructor order at translation time, and Lean refuses to elaborate
the emitted file unless the environment's inductive matches. See
`doc/2026-07-03_direct-recursor-semantics-design.md` (soundness
argument) and the position-directed translation plan, Slice 6.
-/

import Lean
import CryptolToLean.SAWCorePrimitives

open Lean Elab Command in
/-- `saw_ctor_order Foo [Foo.A, Foo.B]` fails elaboration unless `Foo`
is an inductive type whose constructors are exactly the listed names,
in the listed order. The saw-core-lean translator emits one of these
for every datatype whose `@Foo.rec` it emits with SAWCore's positional
argument order; the list is SAWCore's declared constructor order, so a
reordered Lean inductive AND a reordered SAWCore declaration both fail
loudly here instead of silently swapping recursor case handlers. -/
elab "saw_ctor_order " dt:ident " [" ctors:ident,* "]" : command =>
  liftTermElabM do
    let dtName ← realizeGlobalConstNoOverloadWithInfo dt
    let some (.inductInfo iv) := (← getEnv).find? dtName
      | throwErrorAt dt m!"saw_ctor_order: {dtName} is not an inductive type"
    let declared ← ctors.getElems.toList.mapM fun c =>
      realizeGlobalConstNoOverloadWithInfo c.raw
    unless iv.ctors == declared do
      throwErrorAt dt m!"saw_ctor_order: SAWCore declares the constructor \
        order {declared} for {dtName}, but the Lean inductive declares \
        {iv.ctors}. A recursor emitted with SAWCore's positional argument \
        order would silently swap case handlers; fix the drifted \
        declaration rather than removing this check."

namespace CryptolToLean.SAWCoreCtorOrder

/-! Self-tests: the assertion must accept the support library's actual
constructor order and reject a permuted one — an assertion command
that can never fail is no fence. Checked at every `lake build`.

The emitter always writes FULLY QUALIFIED names (command-level
resolution has no expected type to disambiguate short names that
collide with Lean core, e.g. `Stream` and `Either`); the self-tests
mirror that. -/

saw_ctor_order CryptolToLean.SAWCorePrimitives.Num
  [CryptolToLean.SAWCorePrimitives.Num.TCNum,
   CryptolToLean.SAWCorePrimitives.Num.TCInf]
saw_ctor_order CryptolToLean.SAWCorePrimitives.Either
  [CryptolToLean.SAWCorePrimitives.Either.Left,
   CryptolToLean.SAWCorePrimitives.Either.Right]
saw_ctor_order CryptolToLean.SAWCorePrimitives.Maybe
  [CryptolToLean.SAWCorePrimitives.Maybe.Nothing,
   CryptolToLean.SAWCorePrimitives.Maybe.Just]
saw_ctor_order CryptolToLean.SAWCorePrimitives.Stream
  [CryptolToLean.SAWCorePrimitives.Stream.MkStream]

/--
error: saw_ctor_order: SAWCore declares the constructor order [CryptolToLean.SAWCorePrimitives.Num.TCInf,
 CryptolToLean.SAWCorePrimitives.Num.TCNum] for CryptolToLean.SAWCorePrimitives.Num, but the Lean inductive declares [CryptolToLean.SAWCorePrimitives.Num.TCNum,
 CryptolToLean.SAWCorePrimitives.Num.TCInf]. A recursor emitted with SAWCore's positional argument order would silently swap case handlers; fix the drifted declaration rather than removing this check.
-/
#guard_msgs in
saw_ctor_order CryptolToLean.SAWCorePrimitives.Num
  [CryptolToLean.SAWCorePrimitives.Num.TCInf,
   CryptolToLean.SAWCorePrimitives.Num.TCNum]

/--
error: saw_ctor_order: CryptolToLean.SAWCorePrimitives.seq is not an inductive type
-/
#guard_msgs in
saw_ctor_order CryptolToLean.SAWCorePrimitives.seq
  [CryptolToLean.SAWCorePrimitives.Num.TCNum]

/-! ## Constructor SIGNATURE pins (audit-2 LIB-4)

`saw_ctor_order` compares constructor NAMES in declaration order.
That is the whole check, and it has a blind spot the audit named
precisely: **it says nothing about the fields WITHIN a constructor**,
and five of the six asserted datatypes are single-constructor — so on
exactly the datatypes where the field-order hazard lives, a
name-order assertion is vacuous (a one-element list has one order).

The hazard is concrete. `@Foo.rec` is emitted with SAWCore's
positional argument order, so a minor premise is applied to the
constructor's fields left to right. If this library's
`RecordType.RecordValue : α → β → …` ever drifted to
`β → α → …`, then at `α = β` — a Cryptol record `{a : [8], b : [8]}`
is exactly that — the emitted recursor still TYPECHECKS while
swapping the field and the record tail, silently swapping every
projection. Same shape for `PairType.PairValue`.

Name-order checking cannot see this, so it is pinned directly: each
`example` ascribes the constructor to its expected signature, which
fails to elaborate if the field order, the field types, or the arity
drifts. These run at every `lake build`, alongside the assertions
above.

Scope note: this closes drift in the LEAN realization, which is
where the hazard was demonstrated. A SAWCore-side field reorder is
not covered here — the emitter reads SAWCore's declaration, so it
would emit the new order and this pin would still pass. Closing that
direction needs the emitter to carry per-constructor field
information into the assertion, and is tracked in `TODO.md`. -/

section SignaturePins
open CryptolToLean.SAWCorePrimitives

/-- `RecordValue` takes the field value BEFORE the record tail. -/
example : ∀ (s : String) (α β : Type), α → β → RecordType s α β :=
  fun _ _ _ => RecordType.RecordValue
/-- `PairValue` takes the first component before the second. -/
example : ∀ (α β : Type), α → β → PairType α β :=
  fun _ _ => PairType.PairValue
/-- `TCNum` carries the `Nat`; `TCInf` carries nothing. -/
example : Nat → Num := Num.TCNum
example : Num := Num.TCInf
/-- `Left` carries the α; `Right` carries the β. -/
example : ∀ (α β : Type), α → Either α β := fun _ _ => Either.Left
example : ∀ (α β : Type), β → Either α β := fun _ _ => Either.Right
/-- `Nothing` is nullary; `Just` carries the payload. -/
example : ∀ (α : Type), Maybe α := fun _ => Maybe.Nothing
example : ∀ (α : Type), α → Maybe α := fun _ => Maybe.Just
/-- `MkStream` carries the index function, not a head/tail pair. -/
example : ∀ (α : Type), (Nat → α) → Stream α := fun _ => Stream.MkStream
/-- The record/tuple terminators are nullary. -/
example : EmptyType := EmptyType.Empty
example : UnitType := UnitType.Unit

end SignaturePins

end CryptolToLean.SAWCoreCtorOrder
