# E4 Map Identity Proof Gap

This was formerly a default proof example. It now emits the intended
proof-carrying bounds shape:

- `genWithBoundsM` supplies generated-index evidence.
- `atWithProof_checkedM` consumes explicit `i < 4` obligations.
- The generated outline still contains local `h_bounds_ := by ... sorry`
  placeholders inside `goal`.

The old proof script proves the pre-obligation `genM`/`atWithDefaultM` shape
and is no longer a checked discharge of the current artifact. Closing this
example belongs to the later Lean proof-support phase for direct bounds
obligations, not to Haskell-side arithmetic classifiers or generated
automation.

Linked rows:

- `obligations/vector_at_with_proof`
- `obligations/vector_gen_with_proof`
- `differential/sequence_map_zip`
