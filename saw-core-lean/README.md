# saw-core-lean

A SAW backend that translates SAWCore terms to Lean 4 source.
The generated `.lean` files import a small handwritten support
library (also in this directory) and elaborate under a Lean 4
toolchain via `lake build`.

## Status

Working end-to-end on:

- `write_lean_term` — translate one Term + its type to a
  `noncomputable def`.
- `write_lean_cryptol_module` — translate a Cryptol `.cry` file
  into a Lean `namespace` of `def`s.
- `offline_lean` — emit a SAW proof obligation as
  `def goal : Prop := …` plus a `theorem goal_holds := by sorry`
  stub. Phase 2's `getting-started.md` walks through discharging
  one of these end-to-end with a tactic proof.

What's punted (with diagnostics — translator refuses cleanly):

- `Prelude.fix` — recursive SAWCore terms are rejected. Lifted by
  Phase 5 (recursion design).
- Universe-polymorphic terms (`(t : sort 1) → …`). The translator
  refuses with a `polymorphismResidual` diagnostic.
- Native `Lean.BitVec` binding (currently `bitvector n := Vec n
  Bool`, with `bv*` operations as axioms plus an axiomatic proof
  library matching Rocq's set). The native binding is a Phase 6
  decision.

## Documentation

Top-level docs are the **current** as-of-today reference:

- [`doc/architecture.md`](doc/architecture.md) — design overview.
- [`doc/getting-started.md`](doc/getting-started.md) — a 30-minute
  walkthrough from a Cryptol property to a closed Lean theorem.
- [`doc/contributing.md`](doc/contributing.md) — how to add a
  primitive, extend a soundness gate, write tests.
- [`doc/2026-04-24_soundness-boundaries.md`](doc/2026-04-24_soundness-boundaries.md)
  — canonical trust contract; cites every regression test that
  pins a soundness claim.
- [`doc/2026-05-02_post-audit-plan.md`](doc/2026-05-02_post-audit-plan.md)
  — current plan-of-record.

For independent audit reports, see [`doc/audit/`](doc/audit/).

For the trajectory of how the project got here (failed P4 / P6
attempts, the specialization-mode pivot), see
[`doc/archive/`](doc/archive/).

## Layout

```
saw-core-lean/
├── README.md                 # this file
├── doc/                      # current docs + dated trajectory in archive/
├── src/
│   ├── Language/Lean/        # Lean 4 surface-syntax AST
│   └── SAWCoreLean/          # translator
├── lean/                     # support library (Lake project)
│   └── CryptolToLean/
│       ├── SAWCoreScaffolding.lean
│       ├── SAWCoreVectors.lean         # Vec ≡ Vector
│       ├── SAWCoreBitvectors.lean      # bitvector n ≡ Vec n Bool
│       ├── SAWCorePreludeExtra.lean    # iteDep / ite wrappers (L-7)
│       ├── SAWCorePrimitives.lean      # axioms + inductives
│       ├── SAWCoreBitvectors_proofs.lean  # ~15 axiomatic bv lemmas
│       └── SAWCorePrelude_proofs.lean     # round-trip + Nat lemmas
└── smoketest/                # Tasty unit / regression tests
```

## Building

```bash
# Build the saw binary
cabal build exe:saw

# Run smoketest (translator-internal; no Lean toolchain needed)
cabal test saw-core-lean-smoketest

# Run integration suite (saw → emitted Lean → optional lake env lean)
make -C otherTests/saw-core-lean test

# Build the Lean support library directly
( cd lean && lake build )
```

Lean toolchain pinned in `lean/lean-toolchain`
(`leanprover/lean4:v4.29.1`).

## Tests

Three layers:

- `saw-core-lean-smoketest` — Tasty unit tests. Runs in
  `cabal test`. Covers AST / pretty-printer / translator
  internals + the lockdown items L-3, L-6, L-7, L-9, L-10, L-11,
  L-14, L-16.
- `saw-core-lean-tests` — runs the
  [`otherTests/saw-core-lean/`](../otherTests/saw-core-lean/)
  integration suite (one cabal test wrapping `bash test.sh`).
  Pinned `.log.good` and `.lean.good` files; optional
  `lake env lean` elaboration when `lake` is available.
- `intTests/test_lean_*` — bespoke per-test directories. Soundness
  gate-firing tests (`test_lean_soundness_*`), end-to-end semantic
  proofs (`test_lean_offline_proof_t{1,3,4}`,
  `test_lean_walkthrough_proof`).

CI runs all three on every push (`.github/workflows/ci.yml`).
