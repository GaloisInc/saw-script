# Proof Gap: LLVM ChaCha20 core qround c0 (in-place state-update shape)

This directory preserves the discharge architecture for the first of the
EIGHT qround obligations emitted by `workflows/llvm_chacha20_core_verify`
(`qround_c0_LLVM_points-to0`, state positions 0,4,8,12). The other seven
(c1–c3, d0–d3) share the identical shape at different position tuples and
are represented by this row.

## Why this is not just another quarterround row

`proofs/llvm_chacha20_q_eq` discharges the SAME quarterround equation for
the standalone qround function. The core-round emission differs
structurally: the C code updates the 16-word state IN PLACE
(`x[a] += x[b]; …`), so the emitted term contains FOUR CHAINED
`genWithBoundsM` sites — each generates the full updated 16-vector with a
body that dispatches on the SYMBOLIC generation index
(`iteM … (equalNat i' c) …`) between a freshly computed word and a
passthrough select — plus state gathers through
`atRuntimeCheckedM … (bvToNat 32 (bvNat 32 k))` (the state indices arrive
as u32 constants). None of that appears in the standalone-qround emission,
and the rowround-recipe scaffold does not reduce it.

## Discharge architecture (VALIDATED on structural replicas, 2026-07-22)

`completed.lean` here contains the full working architecture; every piece
was validated end-to-end on fast structural replicas of the emitted
spelling:

  * `gen_update_16` — ONE-SHOT collapse: an update-gen dispatching
    `equalNat i' c` between a fresh word and the passthrough select IS
    `Vector.set`. Applied once per update site; the state vector stays
    ABSTRACT, which keeps the normalization proof term small. This is the
    core-round counterpart of the `seq4`/`seq16` abstraction discipline.
  * `genWithBoundsM_pointwise_ok` — the outer all-positions comparison gen
    sequences to a pure `Vector.ofFn` without unfolding `genWithBoundsM`
    at match sites (so the update-gen pattern above stays matchable).
  * `atWithProof_checkedM_ok` / `atRuntimeCheckedM_ok` (+ `bvToNat_bvNat`
    with `Nat.reducePow`/`Nat.reduceLT`) — collapse checked and
    runtime-checked selects on success vectors without unfolding the
    accessor definitions.
  * Per-position bullets reduce the literal-index set-chain selects with
    `Vector.getElem_set` + `Nat.reduceEqDiff` + `reduceIte` — set-select
    reduction must stay OUT of the big normalization pass, else it
    rewrites the SYMBOLIC-index passthrough into an `if` and breaks the
    `gen_update_16` match.
  * `generalize state[k]'(by decide) = x_k` before each `bv_decide` —
    the two sides reach `state[k]` through different bounds-proof terms,
    and bv_decide atomizes syntactically, so proof-variant selects become
    DISTINCT opaque atoms (confirmed: duplicate
    `vecToBitVec state[k]` atoms and a spurious counterexample).
    `generalize` abstracts via kabstract, which matches up to defeq
    (proof irrelevance), unifying the variants. Reproduced and fixed on a
    replica.

Two rejected designs, kept for the record:

  * Elementwise dispatch-tree reduction (instantiate the gen trees at all
    16 positions, big-simp or per-bullet): elaborates, but the kernel
    re-check of the resulting normalization chain exceeds 25 MINUTES
    (measured 2026-07-22; the doubleround wall, worse).
  * `ofFn16_words` literal-vector expansion in the big pass: same
    kernel-bill class.

## The gap is wall-clock budget, NOT a resisting subgoal

With the abstract architecture, the structural replica (two update-gens +
comparison gen + fold, real widths, emitted spelling) closes in seconds.
On the REAL emitted term:

  * the big normalization `simp only` + kernel check alone exceeds 550 s
    (bullets stubbed; measured 2026-07-22);
  * the full row exceeds 25 min;
  * the harness cap is 120 s per Lean process.

The residual cost driver was not isolated (the profiler never reaches its
report inside the cap); prime suspects are conditional-lemma discharger
recursion (`bvToNat_bvNat`, `atRuntimeCheckedM_ok`, `gen_update_16` all
carry side conditions, and the discharger re-enters the full simp set at
every candidate site) and higher-order pattern retries against the four
large gen bodies on every fixpoint revisit.

## Unlock paths (in preference order)

1. **SAW-side compositional split** (same unlock recorded for
   `proof-gaps/llvm_doubleround_itp`): verify `chacha20_core` USING the
   already-verified standalone qround as an override, so the in-place
   state-update shape never inlines into the obligations. Removes all
   eight rows of this gap at once. In progress as of 2026-07-22.
2. Unconditional-lemma variant of the architecture: replace the
   side-condition lemmas with per-literal instances (16 index equations,
   4 `gen_update_16` instances at the row's tuple), eliminating discharger
   recursion; then re-measure.
3. Emission-side: preserve let-sharing / emit `Vector.set` (or an
   equivalent update primitive) directly for the in-place update pattern,
   so the Lean side never has to recognize it from the gen encoding.

`.trust-tier` (native-eval) is staged for when the row is revived: the
four per-position closes use `bv_decide` under the two-tier policy.
