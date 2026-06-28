# saw-core-lean: architecture (as of 2026-05-02)

A SAWCore→Lean 4 translation backend, sibling of `saw-core-rocq`.
This doc is the **current** as-of-today reference. Trajectory
documents that explain how we got here live in `doc/archive/`.

## What it does

Given a SAWCore term (typically produced by translating Cryptol
through `cryptol-saw-core`), emit a Lean 4 file that elaborates
under the handwritten support library at
`saw-core-lean/lean/CryptolToLean/`. The emitted file's
semantics are convertible-equivalent to the SAWCore input
(modulo a documented residual trust list — see
`soundness-boundaries.md`).

Three SAWScript primitives drive the backend:

- `write_lean_term : String -> [(String, String)] -> [String] ->
  String -> Term -> TopLevel ()` — emit one term as a `def`.
- `write_lean_cryptol_module : String -> String ->
  [(String, String)] -> [String] -> TopLevel ()` — emit a whole
  `.cry` file as a Lean `namespace` block of `def`s.
- `offline_lean : String -> ProofScript ()` — emit a SAW proof
  obligation as a `def goal : Prop := ...; theorem goal_holds : goal
  := by sorry` stub the user discharges.

## Translation pipeline

```
SAWCore Term
    ↓
scNormalizeForLean   (specialization to fixed point; opaque set
                      auto-derived + leanOpaqueBuiltins fallback)
    ↓
polymorphismResidual (gate: full term-tree walk; reject sort k>0)
    ↓
SAWCoreLean.Term     (term → Lean.AST)
    ↓
SpecialTreatment     (SAWCore ident → Lean target name)
    ↓
Language.Lean.Pretty (AST → Lean source text)
    ↓
emitted .lean file
    ↓
lake env lean        (verifies type-correctness; not in pipeline)
```

**Specialization-mode** (the design pivot from earlier P4/P6
attempts that lived universe-polymorphic). `scNormalize` unfolds
SAWCore defs to a fixed point before translation, so the
emitted Lean is monomorphic in the universes the translator
handles (`Type 0` and `Prop`). The `leanOpaqueBuiltins` list +
`discoverNatRecReachers` auto-derived set keep selected defs
opaque to prevent unsound recursors from surfacing.

## Module map

```
saw-core-lean/
├── doc/
│   ├── architecture.md       (this file — current reference)
│   ├── getting-started.md    (Phase 2 walkthrough)
│   ├── contributing.md       (how to extend)
│   ├── 2026-04-24_soundness-boundaries.md   (canonical trust contract)
│   ├── 2026-05-05_long-term-plan.md         (current plan-of-record)
│   ├── audit/                (independent audit reports)
│   └── archive/              (dated trajectory docs)
├── lean/CryptolToLean/       (handwritten Lean support library)
│   ├── SAWCorePrimitives.lean         (axiom set: bv ops, Either, …)
│   ├── SAWCorePreludeExtra.lean       (iteDep / ite wrappers)
│   ├── SAWCoreVectors.lean            (Vec n α := Vector α n alias)
│   ├── SAWCoreScaffolding.lean        (Lean Bool / Nat / Int re-exports)
│   ├── SAWCoreBitvectors.lean         (bv-Vec aliases)
│   ├── SAWCoreBitvectors_proofs.lean  (Phase 3b: ~15 axiomatic bv lemmas)
│   └── SAWCorePrelude_proofs.lean     (P3-4: addNat/gen/foldr lemmas)
├── src/SAWCoreLean/          (Haskell translator)
│   ├── Lean.hs               (top-level entry points)
│   ├── Term.hs               (term translation)
│   ├── Monad.hs              (TranslationMonad + errors)
│   ├── SpecialTreatment.hs   (SAW name → Lean target table)
│   └── CryptolModule.hs      (Cryptol-module specific path)
├── smoketest/SmokeTest.hs    (Tasty unit tests)
└── ...
```

The `saw-central` package also has Lean-related code:

- `saw-central/src/SAWCentral/Prover/Exporter.hs` — wires the
  translator into SAWScript primitives. Hosts
  `polymorphismResidual`, `scNormalizeForLean`,
  `discoverNatRecReachers`, `leanOpaqueBuiltins`, the
  `auditPreludePrimitivesForLean` audit, and the
  `iterateNormalizeToFixedPoint` cap-loop.

Tests live across:

- `saw-core-lean/smoketest/SmokeTest.hs` — Tasty unit / regression
  tests. Runs at `cabal test saw-core-lean-smoketest`.
- `otherTests/saw-core-lean/` — integration tests (saw → emitted
  Lean → optional `lake env lean` verification). Runs via
  `cabal test saw-core-lean-tests` or
  `make -C otherTests/saw-core-lean test`.
- `otherTests/saw-core-lean/{shape,saw-boundary,proofs}/` — bespoke
  per-test directories: `shape/` and `saw-boundary/` for the
  lockdown gate-firing tests, `proofs/offline_t{1,3,4}/` and
  `proofs/walkthrough/` for end-to-end semantic verification.

## Soundness boundaries

The full contract is in `2026-04-24_soundness-boundaries.md`.
Quick summary:

- **Translator-time refusals**: `polymorphismResidual` (sort k>0
  binders), `UnsoundRecursor` (Nat/Pos/Z/AccessibleNat/AccessiblePos
  `#rec` survivors), `RejectedPrimitive` (`fix_unfold` and other
  primitives with no proof-carrying interface),
  `scNormalize` 100-iter cap. Each pinned by a regression test.
- **Proof-carrying `Prelude.fix`**: fixed-point terms emit the
  translated body plus an explicit Lean contract such as
  `saw_fix_unique_exists`. The old stream/vector structural helper
  lowerings have been removed; recurrence-specific reasoning belongs in
  Lean-checked proof scripts, not Haskell classifiers.
- **Universe collapse**: `translateSort` maps every non-Prop SAW
  sort to Lean `Type`. Pre-`polymorphismResidual` this would
  weaken; the gate enforces that only Type-0 binders reach
  emission.
- **Bool case order**: SAW's True-first vs Lean's false-first.
  Handwritten `iteDep`/`ite` wrappers in `SAWCorePreludeExtra`
  permute correctly; `iteDep` is opaque under specialization
  (L-16) so bare `Bool#rec` doesn't surface.
- **Documented residual trust**: see
  `2026-05-02_residual-trust.md` for the historical catalog. The live
  backend is moving residual semantic assumptions into explicit Lean
  obligations wherever possible.

## How translation lands in your project

A user writes a `.saw` script that calls one of the three
primitives. SAW emits one or more `.lean` files. The user puts
them in a Lake project that depends on the
`saw-core-lean/lean/` Lake package; `lake build` checks
type-correctness; the `theorem goal_holds := by sorry` stub is
where the user replaces `sorry` with a real tactic proof. The
proof library files (`SAWCoreBitvectors_proofs`,
`SAWCorePrelude_proofs`) are imported via `import CryptolToLean`.

See `getting-started.md` for a complete walkthrough.

## Strategic next steps

The plan-of-record (`2026-05-05_long-term-plan.md`) defines:

- **Recursion**: `Prelude.fix` is now a proof-carrying surface. The
  backend emits generic fixed-point obligations and leaves recurrence
  simplification to Lean-checked proof libraries. Full SHA-512 is
  retained as a stretch scalability probe
  (`stretch/sha512_full_module_probe/`), not as a parity blocker.
  `fix_unfold` still rejects as a raw primitive.
- **Phase 6**: Cryptol surface expansion — fill in primitives
  as demos surface, with auto-detect-missing infrastructure.
  See `doc/audit/2026-05-06_cryptol-coverage-gaps.md` for
  current status.
- **Phase 7**: proof-side tooling — does the saw-core-lean
  project ship a proof library, or punt to downstream users?

The `Lean.BitVec` binding (deferred Arc 3 / Phase 6 decision) is
the strategic alternative to the axiomatic proof library — once
`bvAdd` is bound to `BitVec.add`, the Phase 3b axioms become
Mathlib theorems rather than transposed Rocq proofs.
