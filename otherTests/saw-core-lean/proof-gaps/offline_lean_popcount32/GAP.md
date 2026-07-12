# Popcount32 Proof Gap

This driver is the width-32 version of the popcount recurrence proof shape:

```cryptol
ic = [0] # [ if elt then prev + 1 else prev | elt <- bits | prev <- ic ]
```

It is a realistic stress case, not a small conformance litmus. The backend
should emit the fix/productivity and bounds/indexing obligations plainly, and
Lean-side proof support can later decide whether this proof is practical at
width 32 without native proof shortcuts.

Current status:

- 2026-07-12: the emitted `saw_fix_unique_exists` obligation for this
  recurrence shape is currently unsatisfiable — errors are always fixed
  points of the strict wrapped body. See the 2026-07-12 TODO.md design-gap
  entry and `proof-gaps/cryptol_running_sum_verify/GAP.md`; the contract
  must be revised before this proof is attemptable at any width.
- The default driver remains failing and is classified as stress/proof gap.
- The example must not be made green with `bv_decide`, `bv_check`, native
  proof artifacts, heartbeat inflation, or generated Haskell proof logic.
- Do not refresh the golden merely to hide the old proof failure; review the
  emitted obligation shape first and keep any proof-support blocker visible.

Linked rows:

- `proofs/E5_littleendian` (promoted from `proof-gaps/` 2026-07-12)
- `obligations/fix_wrapped_unique`
- `differential/sequence_append_reverse`
