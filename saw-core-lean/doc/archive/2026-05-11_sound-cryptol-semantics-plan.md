# Plan: sound Cryptol/SAW semantics in Lean

**Date**: 2026-05-11
**Context**: We just deleted two unsound axioms (`unsafeAssert`,
`error_unrestricted`) that papered over Cryptol partiality. 33
driver/proof tests now fail loud at translation time. The auto-emit
prelude and hand library are axiom-clean (only Lean's built-in
`propext`/`Classical.choice`/`Quot.sound`). This plan covers what
comes next.

## Mission

This plan is checked against three constraints:

**(a) Reflects the Rocq backend's purpose.** saw-core-rocq exists to
discharge SAW-emitted verification conditions in Rocq's kernel. We
mirror that purpose for Lean. Where Rocq has a sound design choice
we don't already have, we adopt it. Where Rocq makes a *pragmatic*
choice that's not strictly sound (e.g. its `Axiom error` shape),
we improve on it for Lean.

**(b) Supports using Lean as a SAW proof backend.** SAW emits
proof obligations; Lean discharges them in its kernel. The
translation must preserve enough Cryptol semantics that a Lean
discharge gives genuine evidence about the Cryptol program — no
shortcuts that let Lean prove things SAW couldn't.

**(c) Is sound.** No Lean axioms beyond Lean's stdlib
(`propext`, `Classical.choice`, `Quot.sound`). No definitions
whose meaning is stronger than SAW asserts (e.g. `error α msg =
default` would conflate SAW's stuck-error term with a specific
value SAW doesn't pin down).

## The core principle

**Emit a model of Cryptol that includes failure as a first-class
outcome; reason about absence of failure in the discharge.**

Failure modes get distinct, structurally-distinguishable
representations in the Lean target. A SAW verification condition
becomes a Lean proposition about both correctness *and* absence
of failure along the discharged path. Lean's kernel never sees an
axiom that "produces" an inhabitant of every type or asserts an
arbitrary equality — those are exactly the inroads SAW
unsoundness took.

## Two Cryptol partiality flavors, two different remedies

The 33 failing tests touch two flavors of Cryptol partiality.
Despite earlier framing, they are *not* the same problem and
unifying them into one mechanism is overkill.

### Flavor 1 — value-domain `error`

**SAW shape**: `error : (a : isort 1) → String → a`. SAW's
`error α msg` is operationally a stuck term inhabiting α
(Cryptol's universal failure value). Cryptol's typeclass
elaboration sprays it through dead-branch dictionary slots,
appears in division/index-bound failures, etc.

**Rocq's approach**: `Axiom error : forall a (HI : Inhabited a),
String → a` + a `error_realizable := inhabitant` Definition.
Technically still an axiom in the trusted set, but the realizable
form shows it's trivially constructive. Coverage: workflows whose
abstract types have synthesizable Inhabited instances.

**Sound Lean approach**: `error msg : Cryptol α` where
`Cryptol α := Except String α`. The error value is a *real
constructor* of `Cryptol α` (specifically `Except.error msg`),
distinct from any `Cryptol.ok x` value. SAW's stuck-term semantics
maps exactly: `error α msg` becomes the `error`-tagged inhabitant
of `Cryptol α`, distinguishable from every "real" value.

**Why not Lean's `def error := default`?** Because that gives
`error Bool "msg" = false` — Lean conflates SAW's stuck term
with a specific value SAW doesn't pin down. A discharge could
use this conflation to make a step SAW can't justify. The monad
makes the failure case structurally distinct, so no such
conflation is possible.

### Flavor 2 — assertion-without-proof `unsafeAssert`

**SAW shape**: `unsafeAssert : (α : sort 1) → (x y : α) → Eq α x y`.
SAW's normalizer falls back to this when type-level `Nat` arithmetic
doesn't reduce (e.g. `addNat (subNat 16 8) 8 = 16` in a `Vec`
size). SAW *does not* come with a proof — the primitive is an
assertion-without-proof, an "I claim this equality holds, take my
word for it". Translating this as if there's a free proof (axiom,
`sorry`-shaped placeholder, etc.) is unsound: we'd be claiming a
proof exists when SAW didn't actually produce one.

**Correct framing**: SAW's `unsafeAssert α x y` translates to a
**proof obligation** of `Eq α x y` that the Lean discharge must
close. The translation emits the obligation; soundness comes from
the discharge actually proving the equality, never from trusting
SAW's claim.

**Rocq's approach** (which we mirror): tactic call at the call
site:
```
("unsafeAssert", replaceDropArgs 3 $ Rocq.Ltac "solveUnsafeAssert")
```
`solveUnsafeAssert` tries `reflexivity`, `lia`, rewrites on
`addNat`/`subNat`/`mulNat`, then `trivial`. The tactic IS the
attempted discharge — if it succeeds (using only sound tactics),
we've closed the obligation with a real proof term. If it fails,
elaboration errors and the user sees the open obligation, which
they must close manually or fix upstream. **Sound. No axiom.**

**Sound Lean approach**: same — at every SAW call site
`unsafeAssert α x y`, emit `(by saw_unsafeAssert : @Eq α x y)`.
The expression *is the obligation*; `saw_unsafeAssert` is a Lean
tactic that tries `rfl`, `decide`, `omega`, simp on `Nat`-arithmetic
lemmas, etc. Sound tactics only — when the tactic succeeds, the
resulting proof term is genuine. Sound; no monad needed; mirrors
Rocq's architecture.

Key point: we are *not* "translating `unsafeAssert` to a proof".
We are translating it to an *obligation*, paired with a sound
tactic that attempts the discharge. The user retains full
control: if the tactic fails, the user can prove the equality
manually, or push back on SAW to not emit the assertion.

### Why split the two?

- `unsafeAssert` produces a proof (`Eq` value in `Prop`), not a
  Cryptol value. Wrapping in a Cryptol monad would be a category
  error — proofs aren't computational values.
- `error` produces a Cryptol value. The failure case lives in the
  value domain, where a structurally-distinct error constructor
  is the natural fit.
- Mixing the two creates universe headaches and doesn't help
  soundness.

## Concrete design

### Hand library — Cryptol monad

```lean
def Cryptol α := Except String α
abbrev Cryptol.ok    : α → Cryptol α := Except.ok
abbrev Cryptol.error : String → Cryptol α := Except.error
instance : Monad Cryptol := inferInstanceAs (Monad (Except String))
```

Cryptol value types translate `α ↝ Cryptol α`. Cryptol operations
lift via standard monadic combinators. Cryptol's `error msg : α`
translates as `Cryptol.error msg : Cryptol α`.

### Hand library — `saw_unsafeAssert` tactic

```lean
syntax "saw_unsafeAssert" : tactic
macro_rules
  | `(tactic| saw_unsafeAssert) =>
    `(tactic| first | rfl | decide | omega
                    | simp [addNat, subNat, mulNat, …]
                    | trivial)
```

Order matters: cheapest first (`rfl`), then concrete decidable
(`decide`), then `Nat` arithmetic (`omega`), then SAW-specific
rewrites, then `trivial` as a last resort. Mirrors Rocq's
`solveUnsafeAssertStep` set.

### SpecialTreatment for `error`

Translator emits `Cryptol.error` for SAW's `Prelude.error`:

```haskell
, ("error", replace (Lean.App (Lean.Var "Cryptol.error") [Lean.Var "msg"]))
```

(Subject to the actual `replace` shape — we may need a 1-arg
macro that produces a Cryptol-monad application.)

### SpecialTreatment for `unsafeAssert`

Translator emits a tactic call at the call site:

```haskell
, ("unsafeAssert", replaceDropArgs 3
                     (Lean.By (Lean.Tactic "saw_unsafeAssert")))
```

The drop-3-args is critical: SAW emits `unsafeAssert α x y` with
all three args explicit, but the *Lean* tactic produces a proof
of `Eq α x y` directly — we replace the whole 3-arg application
with the tactic.

### What is wrapped, what is not

* **Cryptol-derived value-producing terms** wrap in `Cryptol α`.
  Examples: Cryptol functions, Cryptol arithmetic, Cryptol vector
  operations. Wrap.
* **SAWCore Prelude propositional helpers**: `Eq__rec`, `sym`,
  `trans`, `eq_cong`, `coerce__def`, etc. These produce *proofs*,
  not values. Do **not** wrap.
* **SAWCore types**: `Bool`, `Nat`, `Vec n α`, etc. The types
  themselves don't wrap (they're inhabited by values that wrap).
  Cryptol values *of those types* wrap.

The translator distinguishes: a term whose translation produces a
`Prop`-or-proof shape stays non-monadic; a term that produces a
value (`Bool`, `Vec n α`, etc.) becomes `Cryptol (Bool / Vec n α
/…)`.

## Phase plan

### Phase α: `saw_unsafeAssert` tactic + SpecialTreatment (~3-4 days)

Mirror Rocq's `unsafeAssert` design. No monad work yet; just the
tactic and the call-site emission.

Deliverables:
- `CryptolToLean.SAWTactics` (or similar) module with the
  `saw_unsafeAssert` tactic macro. Includes the SAW-arithmetic
  rewrite lemmas (`addNat_add`, `subNat_sub`, etc.) needed for
  `simp` steps.
- SpecialTreatment for `Prelude.unsafeAssert` flips from `reject`
  to `replaceDropArgs 3 …` (or analogous shape — may need a new
  `UseTactic` treatment variant).
- One restored driver test (e.g. `arithmetic` or `implRev4`) that
  exercises the size-coercion path. Discharge against the
  monomorphic test workflow.

This phase alone unblocks tests whose only Cryptol partiality is
size coercions (probably ~5-10 of the 33 failing tests). The
`error_unrestricted`-needing ones stay blocked pending phase β.

### Phase β: Cryptol monad (~1-2 weeks)

Establish the monad and refactor the translator to emit monadic
Lean for Cryptol value-producing terms.

Deliverables:
- `CryptolToLean.Cryptol` module: `Cryptol α := Except String α`,
  `Monad` instance, common helpers (`Cryptol.bind`-style for
  pattern matching against `Cryptol.ok`).
- SpecialTreatment for `Prelude.error` flips from `reject` to a
  `replace` targeting `Cryptol.error`.
- Translator's per-decl emission learns "Cryptol-value mode" vs
  "SAWCore-proof mode". The auto-emit walker uses the appropriate
  mode per entry.
- Hand-rolled probe + restored driver tests for Cryptol modules
  with error branches.

This phase unblocks the remaining ~20-25 failing tests (modulo
workflows that genuinely depend on unsound semantics; those
should fail correctly).

### Phase δ: full re-validation (~2-3 days)

Re-run the 33 failing tests. Refresh `.lean.good` files for those
that come back online. Inspect any remaining failures and decide
case-by-case whether they're correct loud-failures or further
translator gaps.

Deliverables:
- Test suite back to "1 known pre-existing failure" (the Phase
  1.4 cookbook).
- For each test that's *now* failing legitimately (because its
  Cryptol workflow had an unsound dependency), a documented
  reason and either a refactor or an explicit-proof discharge.

### Phase ε: bonus axiom audit (~1 day)

`vecToBitVec_bitVecToVec` and `bitVecToVec_vecToBitVec` in
`SAWCorePrimitives.lean` are *provable* round-trip theorems
labeled `axiom`. Convert to theorems with proofs. Lower priority
than α-δ but should be done before this work is "complete".

**Total: ~2-3 weeks**, with phase α giving partial coverage
restored in the first week.

## Open implementation questions

1. **Wrap granularity** (user said "don't care"). Default: wrap
   every Cryptol value, optimize later if discharge ergonomics
   suffer.

2. **Universe of the monad** (user said "don't care, whatever
   works"). Default: `Cryptol : Type u → Type u` (universe-poly
   in `α`), inherits from `Except String α`. Should compose
   cleanly with Phase 2 universe machinery.

3. **Discharge ergonomics** (user said "leave for now"). The
   `cryptol_eq` convenience tactic to reduce `f x = Cryptol.ok v`
   to the underlying value equality is a follow-up after core
   works.

4. **Interim coverage policy** (user said "gate Cryptol tests").
   During phase α (with only `unsafeAssert` unblocked), keep
   Cryptol-touching tests gated off; let phase β rolling
   re-enables them.

5. **Should `saw_unsafeAssert` tactic call `decide` first or
   `rfl` first?** Rocq's order: `try reflexivity; try (rewrites;
   simpl; reflexivity; lia); trivial`. So `rfl`-first.
   Replicate.

## Soundness re-check

After full plan:

* No Lean axioms beyond `propext` / `Classical.choice` /
  `Quot.sound`.
* `unsafeAssert` emits a proof obligation at every call site,
  discharged by a sound tactic. When the tactic succeeds, the
  resulting proof term is genuine. When it fails, elaboration
  errors loud and the obligation is visible to the user — never
  hidden behind an axiom.
* `error` produces a structurally-distinguished failure value;
  no Lean fact like `error α msg = default` muddles SAW's
  stuck-term semantics.
* All SAW VCs translate to Lean propositions provable using
  Lean's standard kernel; a successful discharge proves both
  correctness *and* absence of failure along the discharged
  path.

Constraints (a)-(c) all met:

* **(a)** Mirrors Rocq's `unsafeAssert` exactly (tactic-discharged).
  Improves on Rocq's `error` (monad rather than axiom).
* **(b)** Provides a sound, complete target for SAW VCs. Lean
  discharges have genuine semantic content about the underlying
  Cryptol/SAW programs.
* **(c)** Strictly sound. No new axioms; no meaning-shift
  conflating SAW partiality with concrete values.

## Decision: start

Decisions per user:
- (1) `Except String α` ✓
- (2) Universe-poly ✓ (whatever works)
- (3) Wrap every value ✓
- (4) Non-Cryptol entries stay non-monadic ✓
- (5) `cryptol_eq` deferred ✓
- (6) Gate Cryptol tests during phase α-β ✓

Decisions locked. Start with phase α.
