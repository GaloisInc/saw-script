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

Current status:

- The default driver remains failing and is classified as a proof gap.
- The old golden still reflects pre-obligation/defaulting-era helper shapes.
- Refreshing it as green current emission would be misleading until the
  recurrence and bounds obligations are reviewed as the intended artifact.
- Closing this gap belongs to proof-support work, not Haskell recurrence
  classifiers, generated arithmetic proofs, or Lean automation added only to
  make this example pass.

Linked rows:

- `obligations/fix_wrapped_unique`
- `differential/sequence_append_reverse`
- `differential/sequence_take_drop_update`
