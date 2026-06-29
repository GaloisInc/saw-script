# SAW Core Lean Conformance Suite

Run the focused backend conformance suite with:

```sh
make conformance
```

This runs every `drivers/conformance_*` generator check and every paired
`proofs/conformance_*` Lean support-library check. The command is allowed to
fail while the backend is incomplete; its job is to report which supported
SAW surfaces currently do not emit correct Lean.

As of the initial suite consolidation, known broken driver surfaces are:

- `conformance_bitvector`: defined division/remainder cases still expose the
  stripped zero-divisor obligation machinery in the generated golden diff.
- `conformance_scalar`: scalar division/remainder/rational cases likewise need
  principled proof-obligation emission.
- `conformance_stream`: raw `Stream.rec` value results are not adapted back into
  the `Except String` value flow.
- `conformance_vector`: higher-order helper functions for `genM`, `foldrM`, and
  `foldlM` need a principled convention or certificate design.
- `conformance_zero_divisor_obligations`: zero-divisor and reciprocal calls do
  not currently emit the required Lean precondition obligations.

Passing `proofs/conformance_*` files check the Lean support-library semantics
directly. They do not excuse broken generator emission; the driver failures are
the source of truth for backend gaps.
