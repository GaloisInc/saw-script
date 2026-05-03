# Semantic testing — investigation and Phase 3 proposal

*2026-05-02. Investigation triggered by the question "do we have CI
or otherwise tests that the output Lean actually does what we
expect?" — i.e., not just that emitted Lean type-checks, but that
it computes the values Cryptol's semantics specifies.*

## Short answer

**Mostly no.** What we have:

| Test layer | Catches | Misses |
|---|---|---|
| Textual `.lean.good` pinning (otherTests) | Regressions in emitted *string* | Type-correct output that means the wrong thing |
| `lean-elaborate.sh` (`lake env lean` per emitted file) | Type errors | Type-correct-but-wrong-meaning output |
| L-N intTests (gate-firing) | Translator refusals working as designed | Computational behavior of accepted output |
| `intTests/test_lean_walkthrough_proof/proof.lean` | Discharge-time regressions in ONE Bool goal | Everything else |

The L-16 discovery is exhibit A. Every Cryptol `if`/`then`/`else`
was silently swapping `trueCase`/`falseCase` for months — every
test passed. The bug was found by analysis, not by tests.

## Rocq's semantic infrastructure

Rocq has substantially more. The handwritten library is ~2728
lines vs our ~477. The bulk of that delta is **proof** content:

| File | Rocq | Lean | What's there (Rocq) |
|---|---|---|---|
| `SAWCoreBitvectors` | 810 | 34 | ~50 bv lemmas: `bvAdd_comm`, `bvAdd_assoc`, `bvAdd_id_l/r`, `bvNeg_bvAdd_distrib`, `bvXor_*` (assoc/comm/refl), `bvSub_*`, `bvult` properties, etc. |
| `SAWCoreBitvectorsZifyU64` | 377 | — | Zify automation for u64 bv reasoning |
| `SAWCoreVectorsAs*` | 525 | 63 | `gen_sawAt`, `append_cons`, vector lemmas, `Proper` instances |
| `SAWCorePrelude_proofs` | 171 | — | `addNat = +`, `gen_sawAt` round-trip, `append` correctness |
| `SAWCoreScaffolding` | 538 | 14 | Bool/Nat/Int reduction lemmas |
| `CryptolPrimitivesForSAWCoreExtra` | 89 | — | Cryptol-specific reduction lemmas |
| **Total handwritten with proofs** | **~2400** | **~145** | |

What this means in practice:
- A Rocq user proving `(x + y) + z == x + (y + z)` over `Vec n
  Bool` can `apply bvAdd_assoc; reflexivity` and close the goal.
- A Lean user proving the same goal has nothing to apply — `bvAdd`
  is an opaque axiom with no reduction rules and no proven
  associativity.

Rocq's CI **builds** the handwritten library
(`saw-core-rocq-tests` job in `.github/workflows/ci.yml:516`).
That build compiles every theorem; if any breaks, CI fails. So
Rocq has **handwritten-proof regression coverage** even though
its `otherTests/saw-core-rocq/` directory is just textual pin
tests like ours.

What Rocq does NOT have (and we don't either):
- Auto-generated proofs that translated Cryptol property *N*
  matches Cryptol's intended semantics.
- The `test_offline_rocq.tN_prove0.v` files have `Admitted.`
  placeholders, never actual proofs.

## What Phase 3 should add

Two complementary streams of work:

### Stream A: Lean proof library matching Rocq's coverage

Port the Rocq handwritten lemma set to Lean. Most of these can't
be **proved** from our axioms (the axioms have no body); they
become **axioms themselves** — faithful transpositions of SAW's
claims about its primitives. This is exactly what Rocq does at
its trust boundary too: `SAWCoreBitvectors.v` has proofs against
a `BitVector` definition, but the SAWCore-side `bvAdd` is itself
defined in `Prelude.sawcore`, and the proofs verify the
representation-level operation rather than re-proving SAW's
intent.

For Lean, lacking a computable representation, we have two
options:

**(A1) Bind to `Lean.BitVec`** (the Arc 3 / Phase 6 deferred
decision). Then `bvAdd` becomes Lean's native `BitVec.add`, and
all the lemmas above are already in `Std.Tactic.BVDecide` /
`Mathlib.Data.BitVec`. Free coverage; cost is the binding
itself plus regenerating `.lean.good` files.

**(A2) Axiomatize the lemmas.** Add
`lean/CryptolToLean/SAWCoreBitvectors_proofs.lean` declaring
`axiom bvAdd_comm : ∀ w a b, bvAdd w a b = bvAdd w b a`, etc.
User proofs can `apply bvAdd_comm`. Cost: each axiom is on faith;
a wrong axiom would be a soundness violation. Mitigated by
keeping the axiom list small (~20 lemmas) and documented; can be
audited.

I'd recommend **(A2) as a tactical fix, with (A1) as the
strategic plan**. (A2) ships in days; (A1) is multi-week
(regenerate every `.lean.good`, prove `BitVec` ops match SAW
semantics).

### Stream B: Discharge proofs for offline_lean goals

For each `test_offline_lean.tN`, write a `proof.lean` that
discharges the emitted goal. Coverage of t1-t4 (the four Cryptol
property obligations we already pin):

| Goal | Cryptol intent | Tactic to close |
|---|---|---|
| t1: `x == y ==> x + y == x + x` | bv: x = y implies x+y = 2x | needs `bvAdd_idem` axiom; or `cases (bvEq x y)` + reasoning |
| t2: `(a && b) ‖ (a && c) == a && (b ‖ c)` | pure Bool distributivity | `cases <;> rfl` (already in walkthrough) |
| t3: `(x + y) + z == x + (y + z)` | bv associativity | `apply bvAdd_assoc` |
| t4: `(if b then x else y) == (if ~b then y else x)` | pure Bool case-symmetry | `cases b <;> simp` |

After Phase 3, all four would have pinned proofs. A future
translator regression that swaps a case (like L-16) breaks at
least one proof. End-to-end semantic verification.

This goes BEYOND Rocq's coverage — Rocq doesn't prove its
offline_rocq goals; only Lean would. That's because Lean's tactic
language makes the proofs short, while Coq's `lia`/`omega`
stops short of bv reasoning without zify (and zify's another 377
lines of infrastructure).

## Concrete Phase 3 deliverables

In priority order (lowest cost, highest value first):

**P3-1**: `lean/CryptolToLean/SAWCoreBitvectors_proofs.lean` —
~20 axiomatized lemmas matching Rocq's bv set. **Cost**: half a
day. **Soundness cost**: ~20 axioms on faith, each a one-liner
with a clear semantic meaning. Audit-able.

**P3-2**: `intTests/test_lean_offline_proof_t{1..4}/` —
discharge proofs for the four offline_lean goals using P3-1's
lemmas. **Cost**: 1 day. **Soundness benefit**: catches L-16-
style swap bugs, axiom-shape regressions, anything that breaks
semantic correctness of accepted output.

**P3-3**: Wire P3-2 into CI — already covered by the
`integration-tests` job (the new dirs are intTests). Just
making sure they actually run.

**P3-4**: `lean/CryptolToLean/SAWCorePrelude_proofs.lean` —
small file with `addNat = Nat.add`, `gen_atWithDefault`
round-trip, etc. The non-bv equivalents to P3-1. **Cost**: half
a day. Several of these are provable from axioms (rfl); some
need to be axiomatized (round-trips on opaque ops).

**P3-5**: A "decide-driven" smoketest battery — for each
finite-state Cryptol property we ship as a test, write a
discharge proof using only `intro <vars>; decide` or
`cases <;> rfl`. Catches semantic regressions on the simplest
class of property without needing the bv axioms.

**P3-6** (deferred to Phase 6/7): bind `bvAdd`/etc. to
`Lean.BitVec` (Arc 3 decision). This subsumes P3-1 by making
the lemmas provable rather than axiomatic. Multi-week.

## Risk: axiom drift

The biggest soundness concern with P3-1 is that an axiomatized
lemma might be *wrong* relative to SAW's actual semantics. For
each axiom we add, we need:
1. The Rocq counterpart's proof. If Rocq proves it from its
   `BitVector` definition, the lemma is true under SAW's
   intended semantics.
2. A note in the docstring linking to the Rocq proof.

This makes the axiom set a faithful transposition (Rocq proves it;
we transport the result). If a future Rocq audit invalidates one
of these lemmas, our axiom is also wrong — but at least the
inconsistency is visible.

The L-2 / L-8 / L-16 lockdown work establishes the *shape* of our
axioms matches SAW exactly. P3-1 is the analogous *equational*
content: SAW says `bvAdd w a b = bvAdd w b a`; we declare that as
an axiom; user proofs can use it. The Lean side's job is to
faithfully transport SAW's claims, not re-prove them.

## Bottom line

Rocq's coverage we want to match is:
- ~50 bv lemmas (assoc, comm, identity, neg-distrib, etc.)
- Vector / list lemmas
- Bool / Nat reduction lemmas
- A `Proper` discipline so user proofs can `setoid_rewrite`

Lean equivalent at minimum: 50-line `SAWCoreBitvectors_proofs.lean`
+ 30-line `SAWCorePrelude_proofs.lean` + 4 discharge proofs for
test_offline_lean.tN. ~150 lines of new content; days of work,
not weeks. Strategic next step is the BitVec binding (multi-week)
which subsumes the axiomatic version.

The L-16 discovery is the prior-art lesson: textual pinning +
elaboration ≠ semantic correctness. Phase 3 is where that gap
closes.
