# SAW Core Lean Conformance Suite

Run the focused backend conformance suite with:

```sh
make conformance
```

This runs every `drivers/conformance_*` generator check, selected Cryptol-source
feature drivers, selected whole-module extraction drivers, selected
command-level parity drivers (`offline_lean`, `offline_lean_e_series`,
`sawcore_prelude_auto_emit`, and `cryptol_primitives_auto_emit`), every
`saw-boundary/*` expected rejection/obligation check, every paired
`proofs/conformance_*` Lean support-library check, and selected checked
`offline_lean` proof discharges. The command is allowed to fail while the
backend is incomplete; its job is to report which supported SAW surfaces
currently do not emit correct Lean.

As of the initial suite consolidation, known broken driver surfaces are:

- `arithmetic`: legacy Cryptol-source arithmetic examples still expose the
  missing zero-divisor obligation design in generated golden diffs.
- `conformance_bitvector`: defined division/remainder cases still expose the
  stripped zero-divisor obligation machinery in the generated golden diff.
- `conformance_scalar`: scalar division/remainder/rational cases likewise need
  principled proof-obligation emission.
- `conformance_stream`: raw `Stream.rec` value results are not adapted back into
  the `Except String` value flow.
- `conformance_vector`: higher-order helper functions for `genM`, `foldrM`, and
  `foldlM` need a principled convention or certificate design.
- `conformance_vector_zip`: direct SAWCore `zip` truncation/projection coverage
  is source-proved by SAW, but emission hits the same raw function result to
  `Except String` adaptation gap when constructing its input vectors with
  `genM`.
- `conformance_zero_divisor_obligations`: zero-divisor and reciprocal calls do
  not currently emit the required Lean precondition obligations.
- `cryptol_module_error_string`: whole-module extraction for a safe division
  helper currently emits unchecked bitvector division rather than a nonzero
  obligation.
- `cryptol_module_rational`: whole-module extraction for rational literals
  currently emits `ratio` without the required nonzero denominator obligation.

Passing `proofs/conformance_*` files check the Lean support-library semantics
directly. They do not excuse broken generator emission; the driver failures are
the source of truth for backend gaps.

The selected non-`conformance_*` proof fixtures check the actual
proof-discharge workflow: SAW emits a Lean obligation, a separate proof file
imports the tracked emitted artifact unchanged, and the harness audits the
completed theorem's axioms.

Passing `saw-boundary/*` files check that unsupported or partial SAWCore
surfaces fail loudly or emit explicit obligations instead of silently producing
semantically different Lean.

Boundary coverage currently includes:

- Unsupported recursors or recursion forms: `Bool.rec`, `Nat.rec`, `Z.rec`,
  accessibility recursors, and unsupported `fix` unfold shapes.
- Raw-position partiality/obligation behavior: polynomial literals and generic
  `fix` obligations.
- Unsupported source forms: Cryptol algebraic enums.
- Mapped-but-unsupported primitives that must reject explicitly rather than
  leaking unmapped names or ad hoc semantics: `intAbs`, `intMin`, `intMax`,
  vector `head`/`tail`/`EmptyVec`/`scanl`, with-proof vector variants,
  SMT-array primitives, and under-applied `unsafeAssert`.
- SAW-internal proof primitives and lemma axioms that must not be emitted as
  trusted Lean axioms without checked realizations, including representative
  Nat, vector, bitvector, coerce, UIP, and size-bound assertion cases.

Additional conformance coverage added after the initial consolidation:

- `conformance_boolean`: `not`, `and`, `or`, `xor`, and `boolEq`.
- `conformance_bitvector_conversions`: `bvToNat`, `bvToInt`, `sbvToInt`,
  `bvNat`, and `intToBv`.
- `conformance_core`: `id` and `sawLet`.
- `conformance_error`: unreachable Cryptol `error` branches and the checked
  `saw_throw_error` / `iteM` support behavior.
- `conformance_proof_obligations`: fully-applied `unsafeAssert` feeding
  `coerce`, pinned as a visible Lean equality obligation.
- `conformance_scalar_extra`: defined Nat, Int, IntMod, and Rational operations
  not covered by the division-focused scalar fixture.
- `conformance_string_bytes`: `bytesToString` on a concrete ASCII byte vector.
- `conformance_vector_zip`: SAWCore `zip` truncation and pair projection.
