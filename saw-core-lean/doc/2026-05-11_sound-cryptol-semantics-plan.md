# Plan: sound Cryptol/SAW semantics in Lean

**Date**: 2026-05-11
**Context**: We just deleted two unsound axioms (`unsafeAssert`,
`error_unrestricted`) that papered over Cryptol partiality. 33
driver/proof tests now fail loud at translation time. The auto-emit
prelude and hand library are axiom-clean (only Lean's built-in
`propext`/`Classical.choice`/`Quot.sound`). This plan covers what
comes next.

## Core principle

**Emit a model of Cryptol that includes failure as a first-class
outcome; reason about absence of failure in the discharge.**

The mistake we just deleted was to model failure as "every type has
a bottom inhabitant" via an unsound Lean axiom. The principled model
is the opposite direction: enrich the value domain with an explicit
failure case (`Except String α`) so that Cryptol's partial operations
have somewhere principled to go when they fail, and verification
conditions become "this computation succeeds *and* produces v",
which inherently includes "no failure occurs anywhere along the
way".

This gives us soundness for free: a Lean proof of "`f x = Cryptol.ok
v`" can only succeed if `f x` actually evaluates to `Cryptol.ok v`,
which can only happen if no `error` or failing `unsafeAssert` ever
fires inside `f`. The discharge *proves the absence of failure* as
part of proving the equality. No axiom-inhabits-everything games;
just standard inductive equality on the enriched domain.

## Goal

Use Lean as a proof backend for SAW — discharge SAW-emitted
verification conditions in Lean's kernel. The translation must
preserve Cryptol's semantics including failure, so that a Lean
discharge gives genuine evidence about the Cryptol program.

## What broke and why

The 33 failing tests touch two flavors of Cryptol partiality. Under
the old design they looked like two different problems requiring two
different fixes; under the unified model they're both instances of
"this operation can fail — model the failure path".

### Cryptol value-level errors

**Symptom**: Cryptol expressions can fail (division by zero,
out-of-bounds access, exhaustive-pattern failure, dead typeclass
branches). SAW preserves the error structure. The old translation
forced `error msg : α` to inhabit *every* Lean type via the
`error_unrestricted` axiom — collapses Lean's logic.

**Where it surfaces**: any Cryptol code that has an `error` branch
— which after typeclass elaboration is **most Cryptol code**.
Cryptol's dictionaries emit `error α "invalid instance"` in dead
branches of `Eq`, `Ord`, `Ring`, etc. So even "non-erroring"
Cryptol modules emit `error_unrestricted` references after SAW
specialization.

### `unsafeAssert` size-coercion residuals

**Symptom**: Cryptol has dependent types over `Nat`-typed sizes
(`[n]Bit`). SAWCore's normalizer reduces type-level `Nat` arithmetic
but not always to a concrete value. When SAW can't prove `addNat
(subNat n m) m = n` at the type level, it falls back to `coerce
(Vec _ _) (Vec _ _) (unsafeAssert Num _ _) v` to bridge the two
indexed `Vec` types. Translating `unsafeAssert` as a Lean axiom
asserted *arbitrary equalities*, which lets you fabricate any
equation including `True = False`.

Under the unified model, `unsafeAssert` is also a partial operation:
"check that x and y are equal; if so, produce a proof; if not, fail".
Same monad as `error`. No second mechanism needed.

## Design: the Cryptol monad

```lean
def Cryptol α := Except String α
def Cryptol.ok    : α → Cryptol α := Except.ok
def Cryptol.error : String → Cryptol α := Except.error
instance : Monad Cryptol := …
```

Cryptol value-types translate as `α ↝ Cryptol α`. Cryptol operations
become monadic. Cryptol's `error msg` becomes `Cryptol.error msg`.

`unsafeAssert` becomes a `DecidableEq`-backed partial check that
lives in the same monad:

```lean
def unsafeAssert {α : Sort u} [DecidableEq α] (x y : α)
    : Cryptol (@Eq α x y) :=
  match decEq x y with
  | isTrue  h => Cryptol.ok h
  | isFalse _ => Cryptol.error s!"unsafeAssert: values not equal"
```

A SAW-emitted size-coercion `coerce A B (unsafeAssert _ x y) v`
translates to:

```lean
do let h ← unsafeAssert x y
   Cryptol.ok (h ▸ v)
```

**Soundness story** (the same one for both partial flavors):

* The `Cryptol` monad is just `Except String`, a standard inductive.
  No axioms. All equality reasoning uses Lean's native `Eq`.
* `error` and `unsafeAssert` are total Lean functions producing
  `Cryptol α` values; they may produce the `error` branch but they
  never inhabit `α` itself.
* A SAW verification condition `f x = v` (for Cryptol `f`) translates
  to `f x = Cryptol.ok v` (for Lean `f` returning `Cryptol β`). To
  discharge this Lean goal, the user must prove `f x` evaluates to
  the `ok` branch with the specific value `v`. That proof inherently
  rules out every internal `error` or `unsafeAssert`-failure case.

### Concrete behavior on existing workloads

For `arithmetic.t11` (`unsafeAssert Num x__ x__` with both sides
syntactically the same `Num.TCNum (addNat (subNat 16 8) 8)`): Lean's
`Nat.decEq` reduces both sides to `16` (closed-term computation).
`decEq` returns `isTrue rfl`. Monad stays in `ok`. Discharge
proceeds.

For an `addNat (subNat 16 8) 8 = 16` case (different syntactic
forms, equal under `Nat` arithmetic): same — both sides reduce to
`16` via Lean's `Nat` normalization. `isTrue rfl`. Discharge
proceeds.

For a *symbolic* case (`unsafeAssert Num (TCNum n) (TCNum (addNat n
0))` with `n` free): `Nat.decEq` can't reduce `addNat n 0`
symbolically. `decEq` is `isFalse _` from Lean's perspective. Goes
to `error`. The discharge fails — *correctly*, because the SAW
user's "assertion" was not proved.

Workflows that hit this case need to either:
- Refactor to a concrete-size form, or
- Provide an explicit Lean-side proof of the underlying `Nat`
  equality (Lean has `omega`, `decide`, `Nat.sub_add_cancel`, etc.),
  feeding into the discharge.

### What this doesn't cover (out of scope)

* SAW's `unsafeAssert (sort 0) Bool Nat` shape — asserting two
  *types* are equal as values at sort 0. `DecidableEq (sort 0)`
  doesn't exist in Lean (universe issue + no decidable equality
  on `Type` in general). That call would fail to typecheck, which
  is correct: SAW's claim that `Bool = Nat` is false, and there's
  no honest Lean rendering of it. If SAW ever emits this from a
  real workflow, it's a SAW bug.

## Phase plan

### Phase α: Cryptol monad infrastructure (~2 days)

Establish `Cryptol α := Except String α` and friends in the hand
library. Validate end-to-end on hand-written Lean discharges that
use the monadic shapes.

Deliverables:
- `CryptolToLean.Cryptol` module with `Cryptol`, `ok`, `error`,
  `Monad` instance.
- `unsafeAssert` as a `DecidableEq`-backed Cryptol-monadic
  function.
- Hand-rolled probe: a small Cryptol-shaped def + discharge,
  demonstrating "discharge proves the no-failure case".

### Phase β: translator monadic emission (~5-10 days)

Modify the auto-emit walker and term translator to produce
monadic Lean output for Cryptol-derived terms. Every Cryptol
value-type wraps in `Cryptol α`; every operation lifts.

Deliverables:
- `SAWCoreLean.Term` understands "this expression is Cryptol-side,
  emit in the monad" vs "this expression is SAWCore-propositional,
  emit non-monadically". The split corresponds roughly to: terms
  reachable from a `Cryptol*` SAW module's defs (monadic) vs.
  terms from `Prelude` like `Eq__rec`, `sym`, etc. (non-monadic,
  these are proof helpers, not Cryptol values).
- SAW's `Prelude.error` and `Prelude.unsafeAssert` SpecialTreatment
  flips from `reject` to monadic emissions targeting the hand
  library.
- New driver test: round-trip a small Cryptol module through the
  monadic translation, discharge a representative goal.

Open implementation question: do we wrap *every* Cryptol value or
only at function boundaries? Wrapping every value is uniform but
heavy. Wrapping at boundaries is lighter but needs a clean
delimitation. Tentative answer: wrap every value, optimize later
if discharge ergonomics suffer.

### Phase δ: re-validate the test suite (~2-3 days)

With α and β landed, re-run the 33 failing tests.

Most will come back online with their `.lean.good` files
regenerated to the monadic shape. Some may remain failing — those
are the workflows whose Cryptol code can fail in a way the
discharge can't rule out (e.g. genuinely-symbolic size mismatches).
Those are *correct* failures and the affected workflows need
refactoring or richer discharge proofs upstream.

### Phase ε: clean up provable-as-theorem axioms (~1 day)

`vecToBitVec_bitVecToVec` and `bitVecToVec_vecToBitVec` in
`SAWCorePrimitives.lean` are *provable* round-trip theorems
currently labeled `axiom`. Prove them. Lower priority than
α-δ but should be done.

## Open decisions before phase α

1. **Monad type**: `Except String α` (preserves error message) vs
   `Option α` (lossy, simpler). Recommend `Except String α` —
   the message carries context that's useful for debugging
   discharge failures, and Lean's tactic ecosystem for `Except`
   is mature.

2. **Universe of the monad**: `Cryptol.{u} : Sort u → Sort u`?
   `Except` in Lean is `Except ε α` with `α : Type u`. So Cryptol
   values stay in `Type u`, which matches Phase 2's universe
   machinery.

3. **Wrap granularity**: every Cryptol value vs. only at function
   boundaries. Recommend: every value, uniform soundness.

4. **Should non-Cryptol SAW Prelude entries stay non-monadic?**
   `sym`, `trans`, `Eq__rec`, etc. — these are propositional, not
   computational. Yes, stay non-monadic. The translator needs a
   clean way to tell them apart from Cryptol-side terms.

5. **Discharge ergonomics**: do we want a `cryptol_eq` tactic that
   mechanically reduces a goal `f x = Cryptol.ok v` to the
   underlying `α`-equality after proving "no failure"? Tentative
   answer: yes, but in a follow-up after the core is working.

6. **Interim coverage policy**: zero Cryptol-touching tests during
   α-β (~1.5 weeks), or gate them off so non-Cryptol tests stay
   live? Recommend: gate them. The auto-emit driver test and the
   non-Cryptol proofs/E* probes can keep running.

## Decision: are we doing this?

Phases α + β + δ + ε is ~1.5-2 weeks. End state:

* `Cryptol α := Except String α` is the value domain.
* SAW VCs translate to `f x = Cryptol.ok v` style goals.
* Discharges prove correctness AND absence of failure.
* Lean kernel stays axiom-clean.
* The Cryptol/SAW workflow that previously needed unsound axioms
  now has principled sound foundations.

If we agree: pick (1)-(6) and start phase α.
