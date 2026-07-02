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

- The default driver remains failing and is classified as stress/proof gap.
- The example must not be made green with `bv_decide`, `bv_check`, native
  proof artifacts, heartbeat inflation, or generated Haskell proof logic.
- Do not refresh the golden merely to hide the old proof failure; review the
  emitted obligation shape first and keep any proof-support blocker visible.

Linked rows:

- `proof-gaps/E5_littleendian`
- `obligations/fix_wrapped_unique`
- `differential/sequence_append_reverse`
