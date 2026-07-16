# Proof Gap: LLVM Popcount (Hacker's Delight vs recursive spec)

The `workflows/llvm_popcount_verify` row emits the obligation comparing
the C bit-twiddling `pop_count` against the Cryptol `popCount` spec.
The spec is the self-referential comprehension

```cryptol
popCount bits = ic ! 0
  where ic = [0] # [ if elt then prev + 1 else prev
                   | elt <- bits | prev <- ic ]
```

## Status 2026-07-15 (post Slice R2): the fix side is dischargeable; the remaining gap is the SWAR equivalence itself

The recurrence-class blocker that used to define this row is gone.
The emitted obligation now carries `saw_fix_bounded_choose` + a
per-instance `saw_fix_bounded_productive` placeholder (OP-3 successor,
Slice R2), and the IDENTICAL popcount fix shape in this artifact is
discharged end-to-end elsewhere in the suite by the R2 recipe:

- `proofs/offline_lean_popcount32` — same shape, W=32/N=33,
  pure-Cryptol pipeline (foldlM spec side);
- `proofs/E6_popcount_bridge` — same shape, W=3/N=5/K=4.

Applying that recipe here (pcBody / pc_h_prod / pc_choose_eq) is
routine and reduces this goal to

```
bvEq 32 (swar x) (pcChain x 32)
```

for SYMBOLIC `x : Vec 32 Bool`, where `swar x` is the LLVM side's
Hacker's Delight computation (`bvAnd`/`bvShr`/`bvAdd`/`bvMul` chains
through the 0x55555555 / 0x33333333 / 0x0F0F0F0F / 0x3F masks) and
`pcChain x 32` is the naive conditional-increment chain. That residue
is a genuine 32-bit SWAR-popcount correctness theorem — NOT
fix-realization plumbing — and it is the sole remaining blocker:

- the R2 recipe's spec-side bridge (`foldlM_pure_eq_foldl` +
  `foldl_eq_natRec_atWithDefault`) does not apply: this LHS is not a
  fold over the bits, it is word-level arithmetic on the 32-bit value;
- the trust policy forbids `bv_decide` / `bv_check` /
  `native_decide`, the standard ways to close exactly this kind of
  fixed-width bit-twiddling equivalence;
- the library has no checked lemma ladder for masked partial-sum
  invariants (the "each 2/4/8-bit field holds the popcount of its own
  bits" induction) over `Vec`/`bvAdd`/`bvAnd`/`bvShr`/`bvMul`.

What a real discharge needs (either one):

1. a manual SWAR correctness ladder in Lean: state the field-wise
   popcount invariant, prove each mask step preserves it (a
   substantial, self-contained bitvector development — dozens of
   checked lemmas about masked adds at field widths 2/4/8/16/32),
   then bridge the final `0x3F`-masked sum to `pcChain x 32`; or
2. a sanctioned checked decision path for fixed-width goals — a
   trust-policy decision, not a proof-support task.

Until one of those exists, do not force this row: no `bv_decide`, no
`native_decide`, no golden refresh to hide the failure, and no
`sorry`-shaped bridge lemmas.

History note (2026-07-15, original row creation): the driver's comment
long promised a discharge at `proofs/llvm_popcount_eq/proof.lean` that
never existed — the promise predated the understanding that this spec
shape is recurrence-class. At that time the blocker was the
unsatisfiable `saw_fix_unique_exists` contract; Slice R2 has since
replaced that contract, and the acceptance-ladder rows this note used
to cite as gaps (`cryptol_running_sum_verify`,
`offline_lean_popcount32`) both now live under `proofs/`.
