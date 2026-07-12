# Running Sum Recurrence Proof Gap

This driver emits the intended proof-carrying shape for a small recursive
Cryptol comprehension:

```cryptol
sums = [0 : [32]] # [ s + x | s <- sums | x <- xs ]
```

The example is useful because it is the small version of the popcount-style
recurrence shape. The backend should emit the recurrence/fix and indexing
contracts plainly; Lean-side proof support should later prove that the
recursive comprehension agrees with the explicit indexed sum.

Current status (2026-07-12):

- The driver itself now passes: the golden matches current emission and the
  artifact elaborates with the intended checked-bounds and
  `saw_fix_unique_exists` obligation shape.
- The proof CANNOT currently be discharged, and not for proof-support
  reasons: the emitted `saw_fix_unique_exists` obligation is unsatisfiable
  for this body. The contract's uniqueness clause quantifies over all
  `Except` values, and the emitted body propagates `Except.error` through
  its element binds, so every error is a fixed point. See the 2026-07-12
  TODO.md entry ("`saw_fix_unique_exists` is unsatisfiable for every strict
  wrapped fix body") for the kernel-checked counterexample.
- Closing this gap requires a contract design revision (uniqueness among
  pure fixed points, with a soundness argument), then proof-support work
  for the revised obligation. Do not attempt a completed-outline proof of
  the current artifact; the embedded `h_fix_unique_` obligation is false.
- Do not close it with Haskell recurrence classifiers, generated arithmetic
  proofs, or Lean automation added only to make this example pass.

Linked rows:

- `obligations/fix_wrapped_unique`
- `differential/sequence_append_reverse`
- `differential/sequence_take_drop_update`
