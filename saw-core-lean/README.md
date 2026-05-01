# saw-core-lean

A SAW backend that translates SAWCore terms to Lean 4 source. The
generated `.lean` files import a small handwritten support library
(also in this directory) and elaborate under a Lean 4 toolchain via
`lake build`.

## Status

Working end-to-end on the driving demo (`saw-lean-example/`),
including a fully-translated polymorphic Cryptol module. Built on
the **specialization-mode** architecture: the translator runs
`scNormalize` on each user term to a fixed point, leaving only
SAWCore primitives / inductives / recursors as residuals — and
those resolve against a small handwritten Lean realisation
(`lean/CryptolToLean/SAWCorePrimitives.lean`).

What works:

- `write_lean_term` — translate one Term + its type to a
  `noncomputable def`.
- `write_lean_cryptol_module` — translate a Cryptol `.cry` file
  into a Lean `namespace` of `def`s.
- `offline_lean` — emit a goal as `def goal : Prop := …` plus a
  `theorem goal_holds := by sorry` stub.
- Specialization on monomorphic instances (concrete vector
  lengths, concrete bitvector widths) and on Cryptol modules with
  ordinary `{a}`-polymorphism over `Type 0`.

What's punted:

- `Prelude.fix` — recursive SAWCore terms are rejected, mirroring
  the Rocq backend.
- Universe-polymorphic terms (`(t : sort 1) → …`). The translator
  refuses with a clear `polymorphismResidual` diagnostic. See
  `doc/2026-04-23_specialization-approach.md` for the rationale
  and `saw-core-lean-p4-wip` for the parked alternative.
- Native `Lean.BitVec` binding (currently `bitvector n := Vec n
  Bool`). Documented as a future-arc tradeoff in
  `doc/2026-05-01_status-and-next-steps.md` §3 Arc 3.

## Layout

```
saw-core-lean/
├── README.md
├── doc/                                 # design + audit docs (chronological)
├── src/
│   ├── Language/Lean/                   # Lean 4 surface-syntax AST
│   └── SAWCoreLean/                     # translator
└── lean/                                # support library (Lake project)
    └── CryptolToLean/
        ├── SAWCoreScaffolding.lean      # Bit alias
        ├── SAWCoreVectors.lean          # Vec ≡ Vector
        ├── SAWCoreBitvectors.lean       # bitvector n ≡ Vec n Bool
        ├── SAWCorePreludeExtra.lean     # iteDep / ite (case-permuted)
        └── SAWCorePrimitives.lean       # axioms + inductives for
                                         # SAW primitives that survive
                                         # scNormalize
```

## Demo

`saw-lean-example/demo.saw` (project-root sibling) drives the
backend on `rev.cry`. It produces `idBool.lean`, `implRev.lean`,
`Rev.lean` (full polymorphic Cryptol module), and two
`*_prove0.lean` goal stubs from `offline_lean`. All elaborate under
`lake env lean` against the support library here.

## Tests

Two layers, both hooked into existing SAW conventions:

- `saw-core-lean-smoketest` — Tasty test suite, runs as
  `cabal test saw-core-lean-smoketest`. Fast, no Lean toolchain
  needed; covers AST/pretty-printer/translator-internals.
- `intTests/test_lean_*/` — integration tests via the same
  `intTests/IntegrationTest.hs` harness used by the rest of the
  SAW project. Each directory pins both saw stdout (`*.log.good`)
  and emitted `.lean` files (`*.lean.good`), and optionally runs
  `lake env lean` on the output (skipped cleanly if `lake` isn't
  on PATH). See `intTests/support/test-lean.sh` for the test
  driver.

Per-test-directory `make test` / `make good` / `make clean`
shortcuts wrap the underlying `bash test.sh` invocations.

## Documentation

Read in chronological order; the trajectory itself is part of the
documentation:

- `doc/2026-04-22_lean-backend-design.md` — initial design,
  mirroring the Rocq backend
- `doc/2026-04-22_universe-problem.md` and the
  `2026-04-22_universe-*` family — diagnosis of the Lean
  cumulativity gap
- `doc/2026-04-23_specialization-approach.md` — the architectural
  pivot
- `doc/2026-04-23_stage{1,3}-*.md` — staged plan for the rebuild
- `doc/2026-04-24_audit-*.md` — independent soundness audits
  (consolidated guidance in `doc/2026-04-24_soundness-boundaries.md`)
- `doc/2026-05-01_status-and-next-steps.md` — current snapshot and
  prioritised remaining work

## Building

```
# In the saw-script tree:
cabal build exe:saw saw-core-lean

# In saw-core-lean/lean/, to build the Lean support library:
lake build
```

Bumping the Lean toolchain requires editing
`lean/lean-toolchain` and re-running `lake build`. See the
toolchain pinning discussion in
`doc/2026-04-22_lean-backend-design.md` §8 Q2.
