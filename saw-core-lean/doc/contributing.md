# Contributing to saw-core-lean

This guide covers the common workflows: adding a Cryptol
primitive on the Lean side, extending a soundness gate, and
adding regression tests.

## Setup

```bash
cabal build exe:saw                # build the saw binary
cabal test saw-core-lean-smoketest # run translator-level tests
make -C otherTests/saw-core-lean test  # run integration tests
```

The Lean-only intTests (`intTests/test_lean_*_prop`,
`test_lean_walkthrough_proof`, `test_lean_offline_proof_t{1,3,4}`)
need `lake` on PATH. They self-skip cleanly without it. CI installs
elan in the integration-tests matrix step (`.github/workflows/ci.yml`).

## How to add a new SAWCore primitive

A primitive is a SAW Prelude name with no body (e.g., `bvAdd`,
`gen`, `error`). The translator emits a reference to the name;
your job is to give the reference a Lean target.

Three pieces:

1. **A SpecialTreatment entry** in
   `saw-core-lean/src/SAWCoreLean/SpecialTreatment.hs`. Most
   primitives use `mapsTo sawCorePrimitivesModule "<name>"` so
   the SAW reference becomes `CryptolToLean.SAWCorePrimitives.<name>`.

   ```haskell
   , ("bvNewOp", mapsTo sawCorePrimitivesModule "bvNewOp")
   ```

2. **A matching axiom or definition** in
   `saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean`
   (or a more specific support module). The axiom's signature
   must exactly match SAW's. Cite the SAW Prelude line in a
   docstring.

   ```lean
   /-- SAWCore `bvNewOp w x y` — does <thing>.
   See Prelude.sawcore:NNN. -/
   axiom bvNewOp : (w : Nat) → Vec w Bool → Vec w Bool → Vec w Bool
   ```

3. **Remove it from the exception list** in
   `saw-central/src/SAWCentral/Prover/Exporter.hs`'s
   `leanIntentionallyUnmappedPrimitives` if it was deliberately
   unmapped before. The L-14 smoketest catches new Prelude
   primitives that nobody mapped — but if you're filling in an
   exception, you have to clear it from the list yourself.

The smoketest check
(`every Prelude primitive is mapped or intentional`) verifies
the table stays complete.

## How to add a Cryptol-prelude (Cryptol stdlib) entry

These live under the `Cryptol` SAWCore module, separate from the
`Prelude`. Add to `cryptolPreludeSpecialTreatmentMap` in
`SpecialTreatment.hs`:

```haskell
cryptolPreludeSpecialTreatmentMap = Map.fromList
  [ ("Num",   mapsTo sawCorePrimitivesModule "Num")
  , ...
  ]
```

Most Cryptol-prelude defs unfold under specialization, so the
table is small (a handful of entries — the Num inductive and its
ctors). New entries are needed only when a Cryptol def survives
normalization with no Lean target.

## How to extend a soundness gate

Soundness gates live in two places:

- **Translator-time** (`saw-central/src/SAWCentral/Prover/Exporter.hs`):
  `polymorphismResidual`, `discoverNatRecReachers`,
  `iterateNormalizeToFixedPoint`, `auditPreludePrimitivesForLean`.
- **Translation-emission-time** (`saw-core-lean/src/SAWCoreLean/Term.hs`):
  the `UnsoundRecursor` guard, the `UseReject` SpecialTreatment
  combinator.

When extending or adding a gate, follow the L-N lockdown
discipline:

1. Implement the check.
2. Add a regression test that would fire if the check were
   removed. For translator-time gates, this is usually an
   `intTests/test_lean_soundness_*` directory with a synthetic
   `.saw` driver that triggers the refusal. For
   support-library-level gates (e.g., the L-2 unsafeAssert axiom
   shape), it's a Lean-only intTest with attack/positive `.lean`
   probes.
3. Document in `2026-04-24_soundness-boundaries.md` with a
   citation back to the test path.
4. (For new lockdown items) update `2026-05-02_post-audit-plan.md`
   to record the gap and its closure.

## How to add an integration test

Two patterns:

**SAW-driven** (most common): a `.saw` file under
`otherTests/saw-core-lean/`. Add the file plus a `.log.good`
pinning the SAW stdout, plus `.lean.good` files for each emitted
`.lean`. The framework auto-discovers tests by `*.saw` glob.

```
otherTests/saw-core-lean/
├── test_my_thing.saw           # the SAW driver
├── test_my_thing.log.good      # pinned saw stdout
└── test_my_thing.module.lean.good  # pinned emitted Lean
```

To regenerate references after a change: `make -C
otherTests/saw-core-lean good` (after a clean run-tests). Don't
do this without inspecting the diff.

If `lake` is on PATH and the directory has a `lean-elaborate` flag
file, the framework also runs `lake env lean` on each emitted
`.lean`.

**Lean-only** (for tests that exercise the support library
directly, no SAW involvement): an `intTests/test_lean_*`
directory with a bespoke `test.sh` that runs `lake env lean` on
probe files. Mirror the existing
`test_lean_soundness_error_prop/` or `test_lean_walkthrough_proof/`
patterns.

## How to add a proof of an offline_lean goal

When `offline_lean` emits a Cryptol property as a Lean Prop,
discharging it is now expected (see `getting-started.md` for the
walkthrough). For a regression test:

1. Add `intTests/test_lean_offline_proof_<name>/` with a
   `proof.lean` that copies the goal from
   `otherTests/saw-core-lean/test_offline_lean.<name>_prove0.lean.good`
   verbatim and replaces the `by sorry` with a real tactic proof.
2. The proof can use lemmas from
   `CryptolToLean.SAWCoreBitvectorsProofs` (bv axioms),
   `CryptolToLean.SAWCorePreludeProofs` (Nat/Vector lemmas), and
   the `@[simp]` attributes on `iteDep_True` /
   `iteDep_False`/etc.
3. The bespoke `test.sh` mirrors
   `test_lean_offline_proof_t1/test.sh`.

These tests are the strongest semantic-regression coverage we
have — a translator change that breaks the *meaning* of
emitted output (not just its shape) breaks the proof.

## Style notes

- **Comments explain WHY, not WHAT.** Most non-trivial decisions
  cite a doc or a commit. Keep that discipline.
- **Soundness claims pin tests.** The lockdown principle
  (`2026-05-02_post-audit-plan.md` §"Soundness as the bar") rejects
  comment-grade guarantees. If a comment says "X is safe because
  Y," there should be a test that fires if Y stops being true.
- **Hand-maintained safety lists are last resorts.** Prefer
  auto-derive (`discoverNatRecReachers`) or startup audit
  (`auditPreludePrimitivesForLean`) over textual lists. Where
  textual lists exist (`leanOpaqueBuiltins`,
  `leanIntentionallyUnmappedPrimitives`), document each entry's
  reason.
- **Stable command shapes.** The CI / sandboxed test driver works
  through `make -C` and `cabal test`. New scripts should plug
  into those rather than introducing new invocations.

## What NOT to do

- Don't bypass `polymorphismResidual` or the `UnsoundRecursor`
  guard. They're load-bearing for translator output to mean what
  SAW says it means.
- Don't add `axiom` declarations to support library files
  without a docstring linking to the SAW Prelude line they're
  transporting.
- Don't update `.lean.good` references in bulk after a translator
  change without inspecting the diff. The `make good` shortcut is
  there for convenience but every regenerated file should look
  right.
- Don't introduce new hand-maintained safety lists. If a check
  needs a list, audit it for auto-derive opportunities first.
