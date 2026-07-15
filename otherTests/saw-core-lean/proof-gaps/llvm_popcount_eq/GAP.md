# Proof Gap: LLVM Popcount (Hacker's Delight vs recursive spec)

The `workflows/llvm_popcount_verify` row emits the obligation comparing
the C bit-twiddling `pop_count` against the Cryptol `popCount` spec.
The spec is the self-referential comprehension

```cryptol
popCount bits = ic ! 0
  where ic = [0] # [ if elt then prev + 1 else prev
                   | elt <- bits | prev <- ic ]
```

so the emitted obligation carries `saw_fix_unique_exists` — the
wrapped-fix recurrence class. It elaborates but CANNOT currently be
discharged: the contract is unsatisfiable for strict bodies (errors
are always fixed points), the documented release-0.01 top limitation.
This is OP-3 scope (`doc/2026-07-12_obligation-placement-design.md`
§Instance 3); the acceptance ladder runs through
`proof-gaps/cryptol_running_sum_verify` (small) and
`proof-gaps/offline_lean_popcount32` (this same popcount shape,
pure-Cryptol form) before this LLVM-flavored instance.

History note (2026-07-15): the driver's comment long promised a
discharge at `proofs/llvm_popcount_eq/proof.lean` that never existed —
the promise predated the understanding that this spec shape is
recurrence-class. This GAP row replaces the dead pointer with the
honest state. No `proof.lean` is preserved here because no credible
attempt exists to preserve; write one only when the OP-3 successor
contract makes the obligation dischargeable.
