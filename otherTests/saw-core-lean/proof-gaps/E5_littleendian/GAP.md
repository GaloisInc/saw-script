# E5 Littleendian/Reverse Proof Gap

This was formerly a default proof example. It now emits the intended
proof-carrying bounds shape for nested reverse/indexing:

- `genWithBoundsM` supplies generated-index evidence.
- `atWithProof_checkedM` consumes explicit bounds obligations.
- Derived indices such as `subNat 3 i` produce visible obligations that the
  generated outline leaves as local `h_bounds_ := by ... sorry` placeholders.

The old proof script proves the pre-obligation `genM`/`atWithDefaultM` shape
and is no longer a checked discharge of the current artifact. Closing this
example belongs to the later Lean proof-support phase for derived bounds
obligations, not to Haskell-side arithmetic classifiers or generated
automation.

Linked rows:

- `obligations/vector_at_with_proof`
- `obligations/vector_gen_with_proof`
- `differential/sequence_append_reverse`
- `differential/cryptol_ec_reverse`
