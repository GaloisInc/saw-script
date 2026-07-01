# Contributing to saw-core-lean

This guide covers the common workflows: adding a Cryptol
primitive on the Lean side, extending a soundness gate, and
adding regression tests.

## The gate — `make test-saw-core-lean`

For ANY change touching the Lean backend (translator source,
support library, soundness lockdowns, drivers, proofs), this is
the single command that must pass:

```bash
make test-saw-core-lean
```

It exits non-zero on the first failure. CI runs the same target.

What it covers (all five steps must pass):

  1. Build SAW with current translator changes (`cabal build exe:saw`).
  2. Build the CryptolToLean Lean support library (`lake build`).
  3. Run Haskell-side translator invariants
     (`cabal test saw-core-lean-smoketest`) — pins L-1..L-17.
  4. Run Lean-side driver/proof/shape/saw-boundary tests
     (`cabal test saw-core-lean-tests`) — pins emission shape,
     proof discharges, axiom signatures.
  5. Run general SAW integration tests
     (`cabal test integration-tests`) — catches regressions in
     non-Lean infrastructure that affect the backend transitively.

For faster dev iteration on a focused change, the individual
sub-targets are also available — pick whichever applies to what
you touched:

```bash
cabal build exe:saw                       # SAW binary
( cd saw-core-lean/lean && lake build )   # support library
cabal test saw-core-lean-smoketest        # translator invariants
cabal test saw-core-lean-tests            # Lean-side orchestrator
```

The Lean-side tests need `lake` on PATH (install via elan if
missing). The harness fails loudly when `lake` is missing — no
silent skips. CI installs elan on Linux/macOS automatically;
Windows is currently `continue-on-error: true` per issue #2648.

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

3. **Replace any explicit `reject` entry** in
   `sawCorePreludeSpecialTreatmentMap` (or
   `cryptolPreludeSpecialTreatmentMap`). CG-1 (2026-05-07) made
   any unmapped `ModuleIdentifier` reject by default, so primitives
   that aren't yet wired up are catalogued either as a `reject` with
   a user-meaningful reason or are simply absent from the map and
   land on the default reject. To "fill in" a primitive, swap the
   `reject` for a `mapsTo` (or whatever treatment fits) — there is
   no separate exception list to clear anymore.

The L-14 smoketest
(`auditPreludePrimitivesForLean` —
`every SAW Prelude primitive is mapped or rejects`) verifies the
table stays complete on every run.

## Backend minimality rule

The Haskell backend should stay boring. When adding or changing emission code,
prefer the smallest faithful Lean term plus explicit proof obligations. Do not
add Haskell-side semantic recognizers, generated proof search, defaulting
fallbacks, or special-case rewrites just to make a test elaborate.

If a lowering needs a fact to be sound, emit that fact as a Lean proposition and
route through a checked helper whose type requires exactly that evidence. If a
common obligation should be easy to prove, add a theorem or tactic to the Lean
proof-support library and test it as proof support. Do not hide that reasoning
inside the translator.

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
   `otherTests/saw-core-lean/saw-boundary/*` directory with a synthetic
   `.saw` driver that triggers the refusal. For
   support-library-level gates (e.g., the L-2 unsafeAssert axiom
   shape), it's a Lean-only intTest with attack/positive `.lean`
   probes.
3. Document in `2026-04-24_soundness-boundaries.md` with a
   citation back to the test path.
4. (For new lockdown items) update `2026-05-05_long-term-plan.md`
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
directly, no SAW involvement): an `otherTests/saw-core-lean/{shape,proofs}/*`
directory with a bespoke `test.sh` that runs `lake env lean` on
probe files. Mirror the existing
`otherTests/saw-core-lean/shape/error_prop/` or
`otherTests/saw-core-lean/proofs/walkthrough/`
patterns.

## How to add a proof of an offline_lean goal

When `offline_lean` emits a Cryptol property as a Lean Prop,
discharging it is now expected (see `getting-started.md` for the
walkthrough). For a regression test:

1. Add `otherTests/saw-core-lean/proofs/offline_<name>/` with a
   `proof.lean` that copies the goal from
   `otherTests/saw-core-lean/test_offline_lean.<name>_prove0.lean.good`
   verbatim and replaces the `by sorry` with a real tactic proof.
2. The proof can use lemmas from
   `CryptolToLean.SAWCoreBitvectorsProofs` (bv axioms),
   `CryptolToLean.SAWCorePreludeProofs` (Nat/Vector lemmas), and
   the `@[simp]` attributes on `iteDep_True` /
   `iteDep_False`/etc.
3. The bespoke `test.sh` mirrors
   `otherTests/saw-core-lean/proofs/offline_t1/test.sh`.

These tests are the strongest semantic-regression coverage we
have — a translator change that breaks the *meaning* of
emitted output (not just its shape) breaks the proof.

If the generated outline itself contains local proof holes, add a
`completed.lean` next to `proof.lean` and fill those holes there. Do not
rewrite the obligation to a different theorem. The harness checks the
completed `goal` against the tracked generated `.lean.good` goal by
Lean definitional equality; non-definitional simplifications belong in a
separate Lean proof.

## Style notes

- **Comments explain WHY, not WHAT.** Most non-trivial decisions
  cite a doc or a commit. Keep that discipline.
- **Soundness claims pin tests.** The lockdown principle (the
  L-1..L-17 series captured in `2026-05-05_long-term-plan.md` and
  the residual catalogue in `2026-05-02_residual-trust.md`) rejects
  comment-grade guarantees. If a comment says "X is safe because
  Y," there should be a test that fires if Y stops being true.
- **Hand-maintained safety lists are last resorts.** Prefer
  auto-derive (`discoverNatRecReachers`,
  `discoverEnumEncodingReachers`) or startup audit
  (`auditPreludePrimitivesForLean`,
  `auditCryptolPrimitivesForLean`) over textual lists. Where
  a textual list survives (`leanOpaqueBuiltins`,
  per-primitive `reject` entries in the SpecialTreatment maps),
  document each entry's reason inline.
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
