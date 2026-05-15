# Stress-test plan: Cryptol→Lean discharge walkthroughs

*2026-05-03 — Phase 7 bug-finding campaign.*

## Goal

Drive the Lean backend through real end-to-end discharge workflows
to surface bugs, missing abstractions, and soundness gaps. Each
example follows the canonical Lean-backend use-case:

1. **Cryptol side**: state a property in SAWScript via a Cryptol
   quasi-quote.
2. **SAW export**: `prove_print (offline_lean "name")
   {{ property }}` — SAW translates the goal to a Lean `.lean`
   file with a `theorem goal_holds : goal := by sorry`.
3. **Lean discharge**: replace `sorry` with a real tactic
   script. The proof must close, and it must look *reasonable* —
   with reasonable abstractions, no hacks, no accidental axioms,
   no manual term-mode emission chains.

Each example in the sequence is chosen to exercise a specific
class of translator / support-library behaviour. The walkthrough
is the bug-finding vehicle; when a proof is awkward, the *cause*
of the awkwardness (missing lemma, wrong reducibility, messy
emission, etc.) is the fix to land.

## Principles

- **Every example closes with a real tactic proof (no `sorry`,
  no axiom-via-proof).** Until it closes, the friction tells us
  what's wrong.
- **Prefer small, principled tactic scripts.** If closing needs
  more than ~15 lines of bespoke tactics, the abstraction is
  missing — name the missing piece and add it to the TODO.
- **Every discharge becomes a pinned regression test.** New or
  extend an `otherTests/saw-core-lean/proofs/*` directory; the proof
  runs on every CI pass thereafter.
- **SMT-discharge is not the competition.** Some examples will
  be things SAW's SMT backend could trivially close. That's
  fine — the point is the *Lean-side* discharge ergonomics.
  Other examples will require properties SMT cannot touch
  (symbolic widths, induction); those are also valuable.

## The sequence

The examples are ordered by increasing complexity. Each one
stresses a specific dimension beyond the prior.

### Tier 1 — baseline (should be smooth)

These mirror the existing `test_lean_offline_proof_t{1,3,4}` and
`test_lean_walkthrough_proof` style. They should close cleanly
with the current support library; if any is awkward, that's a
baseline problem to fix first.

**E1. Symbolic-width `bvAdd` commutativity.** A Cryptol property
`\(x y : [w]) -> x + y == y + x` for a fixed concrete `w`. SMT
closes this instantly; Lean closes it via `bvAdd_comm` — one
line. Exercises: offline_lean end-to-end, `open
CryptolToLean.SAWCoreBitvectorsProofs`, named theorem.

**E2. `iteDep` symmetry over bv.** `\(b : Bit) (x y : [w]) ->
(if b then x else y) == (if b then x else y)` — reflexivity under
a conditional. Exercises: the `iteDep` wrapper, `bvEq_refl`,
checks that the translator's `iteDep` wrapping doesn't introduce
inequality by accident.

### Tier 2 — algebraic identities over records / sequences

**E3. Record-field commutativity (Point).** Revive the existing
`point_add_commutes` property via `prove_print (offline_lean
...)` (not just `write_lean_cryptol_module`). Closes by
destructuring records and applying `bvAdd_comm` per field.
Exercises: `RecordType.rec` reduction, nested records.

**E4. Sequence-level bv identity.** `\(xs : [4][32]) -> map
(\x -> x + 0) xs == xs`. Exercises: lifted `bvAdd`, sequence
map, `atWithDefault` under bound. Closes via `Vector.ext` +
`bvAdd_id_r`.

### Tier 3 — spec-vs-impl equivalence

**E5. `littleendian_is_invertable`.** Port this property from
`exercises/functional-correctness/salsa20/Salsa20.cry` (or a
small standalone variant). `\(b : [32]) -> littleendian_inverse
(littleendian b) == b`. Pure algebraic identity with no
concrete inputs; requires reasoning about `join`/`split`/
`reverse` round-trips.

**E6. Two-implementations-of-bit-popcount equivalence.** Write
two Cryptol definitions of popcount over `[8]`:
- `popCount_fold`: a simple comprehension-based fold.
- `popCount_naive`: `ic ! 0 where ic = [0] # [ if b then prev + 1
  else prev | b <- bits | prev <- ic ]` (the `Popcount.cry`
  shape).

Then `property eq bits = popCount_fold bits == popCount_naive
bits`. Tests:
- Phase 5 Slice B (BoundedVecFold) lowering of the naive form.
- Discharge: probably structural induction on the bit-vector or
  the `[n+1]`-comprehension. Hard.

### Tier 4 — induction over symbolic width

**E7. `bvAdd` associativity at symbolic width.** A Cryptol
`primitive` declaration `assoc_for : {w} (fin w) => [w] -> [w]
-> [w] -> Bit` with property `assoc_for x y z = (x + y) + z ==
x + (y + z)`. Via `primitive`, the width stays abstract; SMT
cannot decide (needs a bound), Lean can via `bvAdd_assoc`.

Exercises: the "Proofs involving uninterpreted functions" flow
from the Rocq manual, applied to the Lean side.

**E8. Induction-requiring lemma.** Something like `\(n : Nat)
(x : [8]) -> n * x + n * x == n * (x + x)` where `n : Nat` is
a SAW-side (unbounded) parameter. SMT cannot touch this; Lean
closes via induction on `n`.

### Tier 5 — connecting to mathlib (the "fiat-crypto" analogue)

**E9. `bvAdd` == mathlib `BitVec.add`.** State a Cryptol
property; discharge by `unfold bvAdd; exact (BitVec.add_comm _
_)` or similar. This is the proof-level connection between the
SAW vocabulary and mathlib's BitVec lemmas — the analogue of
"connect to pre-existing Rocq formalizations."

**E10. Full-function correctness against mathlib.** The
ambitious end-state: a Cryptol `popCount : [32] -> [32]` proven
equivalent to `fun bv => Nat.popCount bv.toNat` (or mathlib's
equivalent) via a Lean proof using induction on bit positions.

## Expected bug classes

Each tier is likely to surface different kinds of issues:

- **Tier 1**: stale doc instructions, friction around `open`
  statements, tactic-library shortcomings (naming mismatches,
  missing simp lemmas).
- **Tier 2**: `RecordType.rec` reduction hiccups, lemma gaps
  for sequences, pretty-printing surprise.
- **Tier 3**: Phase 5 lowering quirks, `join`/`split`/
  `reverse` support lemmas absent, `atWithDefault`/`zip`
  unfolding awkwardness.
- **Tier 4**: The `primitive`-based symbolic-width flow may
  not be wired; `Nat`-parameter handling may fail.
- **Tier 5**: `vecToBitVec` / `bitVecToVec` ergonomics,
  missing `_eq_BitVec_*` bridge theorems.

## Protocol per example

For each Ex ∈ E1..E10:

1. Write the SAWScript in
   `otherTests/saw-core-lean/test_offline_lean_<name>.saw`.
2. Run `saw` on it; inspect the emitted `.lean` file. Note any
   translation issues.
3. Create `otherTests/saw-core-lean/proofs/<name>/proof.lean` with a
   discharge attempt. Start with the translated goal verbatim;
   write tactics to close.
4. If the proof is awkward or hits a wall, **stop and diagnose**.
   Fix the support library, the translator, or the tactic
   library. Re-run the proof.
5. Once the proof closes, commit: the SAWScript (pinning the
   emission), the `.lean.good` file (pinning the translation),
   the proof.lean (pinning the discharge).
6. Update this plan with any lessons learned.

## TODOs

See the associated task list for individual E1..E10 items.
