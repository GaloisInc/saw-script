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
  4. Run Lean-side driver/workflow/proof/negative/saw-boundary tests
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

2. **A matching DEFINITION** in
   `saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean`
   (or a more specific support module), semantically equivalent to
   the SAWCore source, with the SAW Prelude line cited in a
   docstring. The trusted base is exactly the two documented
   Vec/BitVec round-trip axioms — a new `axiom` is a TCB expansion
   and needs explicit sign-off plus a STATUS.md entry; every
   current `bv*` op is a real def over `Lean.BitVec`.

   ```lean
   /-- SAWCore `bvNewOp w x y` — does <thing>.
   See Prelude.sawcore:NNN. -/
   noncomputable def bvNewOp (w : Nat) (x y : Vec w Bool) : Vec w Bool :=
     bitVecToVec (BitVec.newOp (vecToBitVec x) (vecToBitVec y))
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
  `discoverNatRecReachers`, `iterateNormalizeToFixedPoint`,
  `auditPreludePrimitivesForLean`.
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
   shape), it's a Lean-only intTest with negative/positive `.lean`
   probes.
3. Document in `archive/2026-04-24_soundness-boundaries.md` with a
   citation back to the test path.
4. (For new lockdown items) record the gap and its closure in
   `TODO.md` (the working roadmap; the historical L-series lives in
   `doc/archive/2026-05-05_long-term-plan.md`).

### Four rules a gate must satisfy (review checklist)

Derived from the categories in
`doc/2026-07-24_semantic-trust-kernel-plan.md` §3. Each rule exists
because breaking it produced a real defect, cited inline. Check all
four when adding or reviewing anything in the trust path
(`saw-core-lean/replay/`, `otherTests/saw-core-lean/support/`).

1. **No skip branch (C1).** A recognizer that cannot answer must
   FAIL, never skip the gate it guards. If a gate is conditional,
   the else-branch must either run an equivalent check or `fail` —
   and if you believe a skip is sound, write the argument in place.
   *Broke twice:* R-1 and A-2 were both `has_goal_def = 0` silently
   disabling the closer↔goal binding. The kernel now treats goal
   presence as an asserted invariant with no flag at all.
2. **No claim without a mechanism (C2).** A doc sentence naming a
   gate is a claim; the identifier must exist. Enforced mechanically
   by `support/doc-claim-lint.sh` for maintained docs — in those,
   `backticks` mean "live identifier in this tree", plain text means
   prose or history. A docstring asserting a code *property* is on
   you: cite what enforces it. *Broke:* A-3 (polymorphismResidual — plain text here
   precisely because it does not exist —
   cited in the trust authority, deleted in May) and
   `saw_stream_realize`'s docstring claiming it consumes a proof its
   body ignores.
3. **Fail closed on tool failure (C3).** Every subprocess capture
   checks exit status **and** output. Empty output from a crashed
   `awk` must never read as a clean result. *Broke twice:* the F1
   lint hardening fixed one call site and did not generalize; RK-7
   was the same bug in the axiom audit.
4. **Ship a mutation the guard catches (C4).** A guard nobody has
   watched fire is a guard that may already be dead. Add the case to
   `support/trust-tier-selftest.sh` and confirm it goes red without
   the guard. *Broke:* four of six negative probes were passing on
   `unknown identifier` because their subjects had been retired —
   they had pinned nothing for weeks.

Two further rules apply to what a check may *rely on*:

5. **Ask Lean, not the text.** Properties of an elaborated
   environment (what a module declared, what it depends on, whether
   it proves the goal, whether it extended the parser) must be asked
   of Lean, not pattern-matched from source. `#check` adds no
   declaration and is therefore never kernel-checked. See the plan
   doc for the migration and for the one honest exception
   (build-affecting options, which cannot be detected after the
   fact).
6. **Obligations must constrain the value (C6).** A contract taking
   a proof argument the realization ignores is erasable: the
   discharge can drop it and every gate stays green.
   `Classical.choose` binds (the predicate is a type-level implicit);
   `Classical.choice` does not (its argument is proof-irrelevant).

### Closing a defect class (the enumeration rule)

When a fix closes a *class* of defects — not just the instance an
audit found — the closing commit must say **how the class was
enumerated, and that sentence must name a mechanism, not a list**.
"I checked all the sites" is the sentence that preceded every one of
the five enumeration failures in
`doc/2026-07-29_convergence-proposal.md` §2 (F-1, F-2, F-5, F-6/F-7,
the Slice-7 lint): each was closed by a hand list that was correct
when written and silent when it rotted. Acceptable mechanisms, in
descending order of strength:

1. **By construction** — the forbidden member is unrepresentable
   (`adaptTo`; zero defects of its class across five audit rounds).
2. **Derived enumeration** — the member list is recomputed from the
   source of truth on every run, and the derivation's own assumption
   is pinned by a test (`contractEmittedNames`, `lintSourceFiles`,
   the `TOMBSTONE:` scan, the waiver-evidence audit, `lib1-census`).
   Name the assumption; deriving moves it, it does not delete it.
3. **Hand list + rot alarm** — only when neither is feasible, a hand
   list whose staleness some check detects loudly (an exact count,
   a dead-entry check). A bare hand list is not a closure; it is the
   defect's next instance with a delay on it.

This is rule 2 ("no claim without a mechanism") applied to closure
claims instead of soundness claims.

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
directly, no SAW involvement): an
`otherTests/saw-core-lean/{negative,support-lemmas}/*` row (data
only — the shared harnesses in `support/` run them; per-subdir
scripts are forbidden by the test.sh design rules). Mirror the
existing `otherTests/saw-core-lean/negative/error_prop/` or
`otherTests/saw-core-lean/proofs/walkthrough/` patterns.

## How to add a proof of an offline_lean goal

When `offline_lean` emits a Cryptol property as a Lean Prop,
discharging it is now expected (see `getting-started.md` for the
walkthrough). For a regression test:

1. Add `otherTests/saw-core-lean/proofs/offline_<name>/` with a
   `proof.lean` that copies the goal from
   `otherTests/saw-core-lean/workflows/offline_lean/test_offline_lean.<name>_prove0.lean.good`
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
  L-1..L-17 series captured in `doc/archive/2026-05-05_long-term-plan.md`
  and the residual catalogue in `2026-05-02_residual-trust.md`) rejects
  comment-grade guarantees. If a comment says "X is safe because
  Y," there should be a test that fires if Y stops being true.
- **Hand-maintained safety lists are last resorts.** Prefer
  auto-derive (`discoverNatRecReachers`,
  `discoverEnumEncodingReachers`) or startup audit
  (`auditPreludePrimitivesForLean`,
  the Prelude audit) over textual lists. Where
  a textual list survives (`leanOpaqueBuiltins`,
  per-primitive `reject` entries in the SpecialTreatment maps),
  document each entry's reason inline.
- **Stable command shapes.** The CI / sandboxed test driver works
  through `make -C` and `cabal test`. New scripts should plug
  into those rather than introducing new invocations.

## What NOT to do

- Don't circumvent the `UnsoundRecursor`
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
