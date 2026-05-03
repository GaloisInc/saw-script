/-
`CryptolToLean.SAWCorePreludeExtra` — handwritten Lean realisations
for SAWCore Prelude constants whose auto-translation would be
semantically wrong or can't elaborate.

Each definition here is paired with a `mapsTo` entry in
`SAWCoreLean.SpecialTreatment.sawCorePreludeSpecialTreatmentMap`
that routes the SAWCore name to its realisation here.

**Soundness discipline.** Every realisation in this file must be
semantically equivalent to the SAWCore source it replaces. If in
doubt, prove the equivalence. See `doc/2026-04-22_soundness.md` for
the rule.
-/

import CryptolToLean.SAWCorePrimitives

namespace CryptolToLean.SAWCorePreludeExtra

/-
## Bool elimination

SAWCore declares `data Bool { True; False; }` — True first. The
auto-generated `Bool#rec1` thus takes `(motive, trueCase, falseCase,
scrutinee)`. Lean's `Bool.rec` takes `(motive, falseCase, trueCase,
scrutinee)` — constructor order swapped.

A faithful translation of SAWCore's `iteDep` / `ite` must permute
the case arguments; otherwise every elimination silently swaps the
True and False branches. Realise them here with the correct
permutation. The `rfl` proofs below verify that the reduction
behaviour matches the SAWCore `iteDep_True` / `iteDep_False` axioms.
-/

/-- `iteDep p b fT fF = p b`, matching SAWCore's argument order
(True case before False case).

Universe-polymorphic in the motive's return sort so callers can
supply a `p` returning `Prop`, `Type 0`, or any higher sort. Lean's
`Bool.rec` is itself universe-polymorphic; the `rfl` reduction
proofs below go through at any `u`. -/
@[reducible] noncomputable def iteDep.{u}
    (p : Bool → Sort u) (b : Bool) (fT : p true) (fF : p false) : p b :=
  Bool.rec fF fT b

/-- SAWCore's reduction rule: `iteDep p True fT fF = fT`. Tagged
`@[simp]` so user proofs over translated goals can collapse the
True branch automatically — without this, every `if`/`then`/`else`
in a Cryptol property would stay as a wall of `iteDep` references
even when the scrutinee is concrete. -/
@[simp] theorem iteDep_True.{u} (p : Bool → Sort u) (fT : p true) (fF : p false) :
    iteDep p true fT fF = fT := rfl

/-- SAWCore's reduction rule: `iteDep p False fT fF = fF`. -/
@[simp] theorem iteDep_False.{u} (p : Bool → Sort u) (fT : p true) (fF : p false) :
    iteDep p false fT fF = fF := rfl

/-- Non-dependent SAWCore `ite : (a : sort 1) -> Bool -> a -> a -> a`,
matching SAWCore's argument order: True case before False case. -/
@[reducible] noncomputable def ite.{u} (a : Sort u) (b : Bool) (x y : a) : a :=
  Bool.rec y x b

/-- `ite` agrees with the non-dependent instantiation of `iteDep`. -/
@[simp] theorem ite_eq_iteDep.{u} (a : Sort u) (b : Bool) (x y : a) :
    ite a b x y = iteDep (fun _ => a) b x y := rfl

/-- `ite` reduction on the True scrutinee — derived shortcut so
`simp` collapses non-dependent `ite` directly without bouncing
through `iteDep`. -/
@[simp] theorem ite_True.{u} (a : Sort u) (x y : a) :
    ite a true x y = x := rfl

/-- `ite` reduction on the False scrutinee. -/
@[simp] theorem ite_False.{u} (a : Sort u) (x y : a) :
    ite a false x y = y := rfl

/-! ## Stream scan (Phase 5c / Slice C)

SAWCore's `streamScanl a b f z as` is defined in the SAW Prelude
via `Prelude.fix` for the sake of stream sharing. Mirror Rocq's
hand-rewrite (`SAWCorePreludeExtra.v` `streamScanl`): emit a Lean
definition using structural recursion on the index.

Soundness: the SAW Prelude comment notes "the fixpoint is well
founded because each element only refers to elements with smaller
indices." Our structural recursion makes that productivity
explicit. The two equivalence lemmas (`streamScanl_zero` /
`streamScanl_succ`) hold by `rfl`, mirroring Rocq's. -/

open CryptolToLean.SAWCorePrimitives in
def streamScanl (α β : Type) (f : β → α → β) (z : β)
    (xs : Stream α) : Stream β :=
  Stream.MkStream (streamScanlIdx α β f z xs)
where
  streamScanlIdx (α β : Type) (f : β → α → β) (z : β)
      (xs : Stream α) : Nat → β
    | 0     => z
    | n + 1 =>
        f (streamScanlIdx α β f z xs n)
          (CryptolToLean.SAWCorePrimitives.streamIdx α xs n)

/-- SAWCore's `streamScanl` at index 0 returns the seed.
Mirrors Rocq's `streamScanl_zero`. -/
theorem streamScanl_zero (α β : Type) (f : β → α → β) (z : β)
    (xs : CryptolToLean.SAWCorePrimitives.Stream α) :
    CryptolToLean.SAWCorePrimitives.streamIdx β (streamScanl α β f z xs) 0 = z :=
  rfl

/-- SAWCore's `streamScanl` at index `n+1` is `f` of the prior
element and the corresponding `xs` element. Mirrors Rocq's
`streamScanl_succ`. -/
theorem streamScanl_succ (α β : Type) (f : β → α → β) (z : β)
    (xs : CryptolToLean.SAWCorePrimitives.Stream α) (n : Nat) :
    CryptolToLean.SAWCorePrimitives.streamIdx β (streamScanl α β f z xs) (n + 1) =
    f (CryptolToLean.SAWCorePrimitives.streamIdx β (streamScanl α β f z xs) n)
      (CryptolToLean.SAWCorePrimitives.streamIdx α xs n) :=
  rfl

/-! ## iterNat / iter (Phase 6 / Rocq parity)

Cryptol's `iter` applies `f` to `x` either `n` times (finite) or
returns `x` unchanged (infinite). Mirrors Rocq's
`CryptolPrimitivesForSAWCoreExtra.v`. -/

/-- Apply `f` `n` times. Same as Lean's `Nat.iterate` /
`Function.iterate`. -/
def iterNat {α : Type} : Nat → (α → α) → α → α
  | 0,     _, x => x
  | n + 1, f, x => iterNat n f (f x)

/-- Apply `f` n times for finite `Num`; identity for `TCInf`. -/
def iter {α : Type} (n : CryptolToLean.SAWCorePrimitives.Num)
    (f : α → α) (x : α) : α :=
  match n with
  | CryptolToLean.SAWCorePrimitives.Num.TCNum k => iterNat k f x
  | CryptolToLean.SAWCorePrimitives.Num.TCInf   => x

end CryptolToLean.SAWCorePreludeExtra
