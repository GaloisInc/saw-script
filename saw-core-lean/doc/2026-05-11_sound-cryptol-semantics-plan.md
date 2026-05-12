# Plan: sound Cryptol/SAW semantics in Lean

**Date**: 2026-05-11
**Context**: We just deleted two unsound axioms (`unsafeAssert`,
`error_unrestricted`) that papered over Cryptol partiality. 33
driver/proof tests now fail loud at translation time. The auto-emit
prelude and hand library are axiom-clean (only Lean's built-in
`propext`/`Classical.choice`/`Quot.sound`). This plan covers what
comes next.

**Goal**: use Lean as a proof backend for SAW — discharge SAW-emitted
verification conditions in Lean's kernel. The translation must
preserve SAW (and ultimately Cryptol) semantics, but only "inasmuch
as we want to do this" — fidelity for any aspect of Cryptol that
actually matters for the verification conditions we discharge, not
gratuitously.

## What broke and why

The 33 failing tests split cleanly into two soundness categories.
Each is a distinct problem requiring a distinct fix.

### Problem A: error semantics

**Symptom**: Cryptol expressions can fail (division by zero,
out-of-bounds access, exhaustive-pattern failure, dead typeclass
branches). SAW preserves the error structure. The old translation
forced `error msg : α` to inhabit *every* Lean type via the
`error_unrestricted` axiom — soundly unjustifiable.

**Where it surfaces**: any Cryptol code that has an `error` branch,
which after typeclass elaboration is **most Cryptol code** —
Cryptol's dictionaries emit `error α "invalid instance"` in dead
branches of `Eq`, `Ord`, `Ring`, etc. So even "non-erroring"
Cryptol modules emit `error_unrestricted` references after SAW
specialization.

**Affected tests**: `cryptol_module_*`, `llvm_*_verify`,
`offline_lean_*`, `proofs/*` (most of them).

### Problem B: size-coercion residuals

**Symptom**: Cryptol has dependent types over `Nat`-typed sizes
(`[n]Bit`). SAWCore's normalizer reduces type-level `Nat`
arithmetic but not always to a concrete value. When SAW can't
prove `addNat (subNat n m) m = n` at the type level, it falls
back to `coerce (Vec _ _) (Vec _ _) (unsafeAssert Num _ _) v` to
bridge the two indexed `Vec` types. Translating `unsafeAssert` as
a Lean axiom was unsound.

**Where it surfaces**: any Cryptol code with non-trivial size
arithmetic — slicing, splitting, joining, padding. Very common.

**Affected tests**: `arithmetic` (t11, t12), `implRev4`,
`llvm_eq_u128_verify`, `cryptol_chacha20_core_iterate`, plus
overlap with Problem A in most others.

The two problems share affected tests but require separate
solutions.

## Design space

### For Problem A (error semantics)

#### A1. Monadic semantic domain — `Cryptol α := Except String α`

Wrap every Cryptol value type. `[8]Bit` translates to
`Except String (Vec 8 Bool)`. Operations become monadic: `(+)` on
Cryptol values becomes `Except.bind`-lifted, etc.

```lean
def Cryptol α := Except String α
def ok        : α → Cryptol α := Except.ok
def err       : String → Cryptol α := Except.error
def Cryptol.bind : Cryptol α → (α → Cryptol β) → Cryptol β := …
instance : Monad Cryptol := …
```

* **Pro**: textbook-clean, soundness obvious, no axioms needed.
* **Con**: every translation changes. The auto-emit prelude
  becomes monadic. Proofs about Cryptol values reason about
  `Except.ok x = Except.ok y` rather than `x = y` — adds case
  splits at every `Except` boundary.
* **Pro**: `decide`/`simp` can handle the `Except.ok`/`Except.error`
  cases mechanically when goals concretize.

#### A2. Two-tier domain — partial values for emission, total for
discharge

Translator emits monadic Lean. The first proof step is
`Except.ok`-extracting (a tactic / structural argument that the
witness is in the `ok` branch). Subsequent steps work on the
unwrapped value.

* **Pro**: discharges look like the old non-monadic style after
  the extraction step.
* **Con**: the extraction lemma needs justification per
  translated function. Whose burden — the translator, the hand
  library, the user?

#### A3. Cryptol values stay as-is; errors become opaque "stuck"
terms

Don't wrap. Instead, translate Cryptol's `error α msg` to a
**Lean opaque constant** that we can't reduce. So
`error α "boom" : α` becomes `Cryptol.error α "boom"` declared
opaque. Lean treats it as an unknown value — no axiom-inhabits-
everything, no `False` derivation.

```lean
opaque Cryptol.error.{u} (α : Sort u) (msg : String) : α
```

Wait — `opaque` in Lean *is* effectively an axiom (it asserts
existence of an inhabitant). Same soundness issue. **A3 doesn't
work.**

#### A4. Reject at translation time (status quo of this commit)

The current state. Any Cryptol workflow emitting `error_unrestricted`
fails loud. Sound, but coverage drops to zero for Cryptol-derived
goals.

* **Pro**: simple, immediately sound.
* **Con**: covers ~0% of real Cryptol workflows.

**Recommendation: A1**, with the caveat that it's a substantial
refactor. A2 is a possible follow-up after A1 lands — extraction
lemmas can layer on top of the monadic core.

### For Problem B (size coercions)

#### B1. Lean-side decision procedure

When the translator emits `coerce A B unsafeAssert v` and both
`A` and `B` are `Vec n α` shapes where `n` is computable, replace
`unsafeAssert` with an *actual proof* `(by decide : … = …)` or
`(by omega : … = …)`.

The translator builds the goal `addNat (subNat 16 8) 8 = 16`
explicitly, and Lean's `decide` discharges it via `Nat` arithmetic.

For symbolic sizes (where one of the operands is a free variable),
emit a *deferred* equality goal that the discharge proves with
context.

* **Pro**: principled, sound, mirrors how `Vec` operations are
  proved in Mathlib.
* **Con**: requires the translator to know the structure
  (`addNat`/`subNat` shape recognizers). Symbolic-size case needs
  a coherent "deferred-equality" emission protocol.

#### B2. Lift size-coercions into the Cryptol monad

Combine with A1: size coercion failures *are* Cryptol errors. If
the sizes don't match, return `Except.error "size mismatch"`. So
`coerce A B unsafeAssert v` becomes `Except.error "…"` when the
sizes can't be proved equal.

* **Pro**: unifies A and B into one monadic story.
* **Con**: a *legitimate* size-coercion (where the equality is
  true and provable) gets demoted to a runtime check. Existing
  Cryptol proofs that use the equality structurally would have
  to be rewritten.

#### B3. SAW-side fix: improve the normalizer

The cleanest fix is upstream — make SAW's normalizer better at
reducing `Nat`-arithmetic-on-literal expressions. `addNat (subNat
16 8) 8` *should* reduce to `16` in SAW's normalizer (it's
arithmetic on closed terms). The fact that it doesn't is a SAW
bug.

* **Pro**: most principled — fixes the root cause.
* **Con**: out of scope for saw-core-lean; requires SAW core work.

**Recommendation: B1**, with B3 as a parallel upstream improvement.
B2 is too lossy for the cases where the equality is genuinely
provable.

## Combined plan

### Phase α: hand-library Cryptol monad infrastructure

Establish the `Cryptol` monad and its operators in the hand
library — `Cryptol.SAWCoreCryptolPrelude` or similar — without
yet touching the translator. Validate end-to-end on a handful of
hand-written Lean discharges that use the monadic shapes.

Cost estimate: **~2 days**.

Deliverables:
- `Cryptol α := Except String α` (or final type choice)
- `Monad`, `Functor`, `Applicative` instances
- Cryptol-equivalent `bind`/`map`/`ap`/`pure`
- Cryptol-shape helpers: `Cryptol.guard` for invariant assertions;
  `Cryptol.ofOption` for optional-value cases
- A hand-written probe demonstrating: `Cryptol Bool` equality,
  `Cryptol (Vec n α)` equality, `Cryptol`-bound function chain

### Phase β: translator monadic-rewrite

Modify the auto-emit walker and term translator to produce
monadic Lean output. Every Cryptol-derived term lives in
`Cryptol α`. Every operation is lifted.

Cost estimate: **~5-10 days**. Translator-internal refactor;
touches every emitter.

Deliverables:
- `SAWCoreLean.Term` understands a "monadic mode" and produces
  `Cryptol`-wrapped output when emitting Cryptol-derived terms
- The auto-emit prelude's Cryptol-specific entries (everything
  the Cryptol module touches) emits monadically
- The non-Cryptol SAWCore Prelude (Eq, sym, trans, etc.) stays
  non-monadic — those are propositional, not computational
- New driver test: round-trip a small Cryptol module through the
  monadic translation, discharge a representative goal

Open question: do we wrap *every* Cryptol value or only at
function boundaries? Inside a single `def`, can we work
non-monadically and lift at the boundaries? This decision shapes
how heavy the emission feels.

### Phase γ: size-coercion replacement

Replace SAW's `unsafeAssert`-based size coercions with proof-
backed coercions. The translator recognizes the `coerce A B
unsafeAssert v` shape and substitutes a `Vec.cast`-style emission
backed by a Lean `decide`/`omega`/`Nat.sub_add_cancel` proof.

Cost estimate: **~3 days**.

Deliverables:
- Shape recognizer in the translator for size-coercion patterns
- Hand-library `Vec.castSize`-style helpers built on Lean's
  native `Eq.rec`-on-`Nat`
- For symbolic sizes: a deferred-equality emission protocol —
  the call site emits the equality as an explicit goal that the
  user's discharge has to prove

### Phase δ: re-validate the test suite

With α, β, γ landed, re-run the 33 failing tests. Many should
come back online with their `.lean.good` files regenerated.

Some may still fail — for instance, Cryptol workflows that
intrinsically rely on the unsound axiom (i.e. were proving
"theorems" using `unsafeAssert` directly, without an actual
guarantee of size equality). Those failures are *correct* and
the affected workflows need rework upstream.

Cost estimate: **~2-3 days**, mostly regenerating `.lean.good` files
and inspecting remaining failures.

## Risks and unknowns

### Universe interactions

Phase 2 work made the translator universe-aware. Wrapping Cryptol
values in a monadic `α ↝ Cryptol α` changes the universe shape —
`Cryptol α` has the universe of `α` (plus universe of `String`,
which is fixed). Some care needed to keep universe polymorphism
working through the wrap.

### Auto-emit prelude interactions

The SAW Prelude entries we now auto-emit (Eq__rec, sym, trans,
etc.) are *propositional*, not computational. They shouldn't be
wrapped — `sym` proves equalities, it doesn't produce values that
can error. The translator needs to distinguish "Cryptol value-
producing" (wrap) from "SAWCore proposition-producing" (don't
wrap). The distinction may not be cleanly available at the term
level.

### Discharge ergonomics

Discharges become harder. A goal like `f x = g x` for Cryptol
functions becomes `f x = g x : Cryptol β`. Tactics need to handle
the `Except.ok`/`Except.error` case-split. We may want a `cryptol_eq`
tactic that mechanically reduces to the underlying value equality
in the "no error" branch.

### Cost vs coverage tradeoff

α + β + γ + δ is roughly **2-3 weeks** of work. During that time,
the saw-core-lean backend covers ~0% of real Cryptol workflows.
Worth asking: are there interim shortcuts that maintain *some*
coverage without re-introducing axioms? E.g. only auto-emitting
the non-Cryptol parts of the SAW Prelude, keeping the hand
library clean of axioms, and accepting that "Cryptol module"
translation is broken until α-δ land.

## Decisions to make before starting

1. **Monad type**: `Except String α` vs `Option α` vs a domain-
   specific `Cryptol α`? Recommend `Except String α` — message-
   preserving, standard, has good tactic support.

2. **Wrap granularity**: every Cryptol value vs only at function
   boundaries? Recommend: every value, for soundness uniformity.
   Optimize later if needed.

3. **Size-coercion symbolic-case protocol**: deferred goal vs.
   pre-proved lemmas in the hand library? Recommend: deferred,
   with hand-library helpers for the dominant shapes
   (`addNat-subNat`, `subNat-addNat` cancellation).

4. **Interim coverage policy**: zero coverage until α-δ done vs.
   gate Cryptol-touching tests separately? Recommend: gate
   Cryptol tests, keep non-Cryptol tests (raw SAW, hand-written
   parse_core tests) live.

5. **What about `vecToBitVec_bitVecToVec` / `bitVecToVec_vecToBitVec`?**
   These are *provable theorems* in the hand library currently
   labeled `axiom`. Lower priority than α-γ but should be
   addressed — convert to theorems with proofs. Cost: ~1 day.

## Next step

Decide on items 1-4 above, then start phase α.
