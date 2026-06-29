# SAW Core Lean Conformance Suite

Run the focused backend conformance suite with:

```sh
make conformance
```

This target is intentionally narrow. It runs:

- every `differential/*` true SAW-vs-Lean executable litmus, and
- every `saw-boundary/*` expected rejection or obligation-boundary litmus.

`make conformance` must not run a test merely because it is small, useful, or
green. Positive executable conformance requires a real differential comparison:
SAW must observe an outcome, Lean must observe an outcome from the SAW-Lean
emitted artifact, and the harness must mechanically compare those observations.

It does not run broad legacy examples, whole-module extraction examples, stress
drivers, crypto examples, or selected proof-discharge demos. Those tests remain
useful as integration checks and as sources for new litmus cases, but they do
not belong in the conformance gate. When a large example exposes a real backend
gap, extract the smallest focused `differential/*` or `saw-boundary/*` test that
captures the feature boundary.

It also does not run `drivers/conformance_*` or `proofs/conformance_*` today.
Those directories contain useful litmus candidates and Lean support-library
regression checks, but most of them are not true differential tests: SAW-side
proof plus Lean elaboration plus a separate Lean theorem is not a compared
SAW-vs-Lean observation. Migrate those cases into `differential/*` one feature
family at a time.

The command is allowed to fail while the backend is incomplete; its job is to
report exactly which small supported or boundary surfaces currently do not emit
correct Lean.

Known broken litmus surfaces currently represented by legacy litmus candidates,
not yet by true differential tests:

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

Passing `proofs/conformance_*` files check Lean support-library semantics
directly. They are useful regression tests, but they are not conformance tests
unless paired with a differential harness that observes the emitted artifact.

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

Legacy litmus candidates added after the initial consolidation:

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
