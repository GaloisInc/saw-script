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

/-- `ite` reduction on the True scrutinee — derived shortcut so
`simp` collapses non-dependent `ite` directly without bouncing
through `iteDep`. -/
@[simp] theorem ite_True.{u} (a : Sort u) (x y : a) :
    ite a true x y = x := rfl

/-- `ite` reduction on the False scrutinee. -/
@[simp] theorem ite_False.{u} (a : Sort u) (x y : a) :
    ite a false x y = y := rfl

/-- Wrapped-args version of `ite` for the Phase β translator. Every
SAWCore value-domain expression translates at type `Except String τ`,
so a SAWCore `ite a b x y` arrives here with `b : Except String Bool`
and `x y : Except String a`. The bind chain extracts the scrutinee,
propagates errors short-circuit-style, and returns whichever branch
was selected.

Soundness: the SAWCore semantics is "total selection of one branch"
on a fully defined scrutinee; the wrap version preserves that exactly,
adding the Cryptol-error-semantics propagation when sub-expressions
fail. -/
@[reducible] noncomputable def iteM.{u} (a : Type u) (b : Except String Bool)
    (x y : Except String a) : Except String a :=
  match b with
  | Except.ok v => Bool.rec y x v
  | Except.error msg => Except.error msg

@[simp] theorem iteM_pure_true.{u} (a : Type u) (x y : Except String a) :
    iteM a (Except.ok true) x y = x := rfl

@[simp] theorem iteM_pure_false.{u} (a : Type u) (x y : Except String a) :
    iteM a (Except.ok false) x y = y := rfl

@[simp] theorem iteM_error.{u} (a : Type u) (msg : String) (x y : Except String a) :
    iteM a (Except.error msg) x y = Except.error msg := rfl

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

/-- Closed-form sanity check: prefix-sum of an all-ones `Stream Nat`
gives the index. Audit M-10 (2026-05-06): a `rfl` regression that
fires loudly if the hand-rewritten `streamScanl` body drifts from
SAW's `Prelude.streamScanl` semantics. (The two `streamScanl_*`
lemmas above only state that the recursion unfolds; this pins the
*sum* of three steps.) -/
example :
    CryptolToLean.SAWCorePrimitives.streamIdx Nat
      (streamScanl Nat Nat (· + ·) 0
        (CryptolToLean.SAWCorePrimitives.Stream.MkStream (fun _ => 1))) 3
    = 3 :=
  rfl

/-! ### Cryptol `iterate` (single-stream polymorphic iteration)

Cryptol's `iterate : { a } (a -> a) -> a -> [inf]a`, defined as
`iterate f x = [x] # [ f v | v <- iterate f x ]`, is the canonical
polymorphic stream-corecursion shape. The translator's
`classifyFix` recognizer detects this exact body shape (after
`scNormalizeForLean` unfolds the polymorphic `Prelude.fix`) and
emits a call to `cryptolIterate` here — sidestepping the type-system
challenge of expressing a polymorphic `Prelude.fix` body in Lean.

The structural recursion below makes productivity explicit (each
index reduces to a smaller index), mirroring the `streamScanl`
hand-rewrite. Soundness rests on the same Cryptol-productivity
trust assumption documented in `doc/2026-05-XX_residual-trust.md`. -/

open CryptolToLean.SAWCorePrimitives in
def cryptolIterate (α : Type) (f : α → α) (x : α) : Stream α :=
  Stream.MkStream (cryptolIterateIdx α f x)
where
  cryptolIterateIdx (α : Type) (f : α → α) (x : α) : Nat → α
    | 0     => x
    | n + 1 => f (cryptolIterateIdx α f x n)

/-- `cryptolIterate` at index 0 returns the seed. -/
theorem cryptolIterate_zero (α : Type) (f : α → α) (x : α) :
    CryptolToLean.SAWCorePrimitives.streamIdx α (cryptolIterate α f x) 0 = x :=
  rfl

/-- `cryptolIterate` at index `n+1` is `f` of the prior element. -/
theorem cryptolIterate_succ (α : Type) (f : α → α) (x : α) (n : Nat) :
    CryptolToLean.SAWCorePrimitives.streamIdx α (cryptolIterate α f x) (n + 1) =
    f (CryptolToLean.SAWCorePrimitives.streamIdx α (cryptolIterate α f x) n) :=
  rfl

end CryptolToLean.SAWCorePreludeExtra
