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
- `write_lean_cryptol_primitives_for_sawcore` — regenerate the
  Cryptol primitives module in Lean.
- `offline_lean` — emit a SAW proof obligation as
  `def goal : Prop := …` plus a `theorem goal_holds := by sorry`
  stub. Emission-only: the SAW goal stays unsolved. Phase 2's
  `getting-started.md` walks through discharging one of these
  end-to-end with a tactic proof.
- `offline_lean_replay` — the discharge path: re-emits the goal
  fresh, checks a user-completed Lean proof against it under the
  factored trust kernel (exact-match axiom allowlist, sorry and
  placeholder policy, drift checks), and only on full success
  admits the SAW goal with recorded `LeanReplayEvidence`. Design
  and audit record: `doc/2026-07-16_replay-design.md`.

`Prelude.fix` is handled by proof-carrying emission. The backend emits
the literal fixed-point body plus explicit Lean obligations for the
semantic facts needed to use it; shape-specific helper lowerings such as
`mkStreamFix`, `mkStreamFixPair`, and `genFix` are obsolete and are not
part of the live support library.

What's punted (with diagnostics — translator refuses cleanly):

- Large recursive Cryptol examples still need proof-side recurrence
  libraries over the generic `fix` obligations.
- Bitvector-gated partial recursion (e.g. factorial on `[8]`) and
  polymorphic `Num#rec1` dispatch (e.g. SHA-512 functor) — these
  shapes can't be soundly translated under productivity-only trust;
  refused at translation time with the `RejectedPrimitive`
  diagnostic.
- Universe-polymorphic terms (`(t : sort 1) → …`) — refused with
  `polymorphismResidual`.
- Native `Lean.BitVec` as the `bitvector` TYPE (currently
  `bitvector n := Vec n Bool`; the `bv*` operations are real
  `noncomputable def`s routing through `Lean.BitVec` via the
  `vecToBitVec`/`bitVecToVec` round trip — the two round-trip
  axioms are the documented trusted base).
- **Class-dictionary primitives (`PCmp`, `PEq`, `PRing`,
  `PIntegral`, `PArith`, `PLogic`, …).** Cryptol's class
  dictionaries currently translate as bare SAWCore identifiers
  with no Lean-side `SpecialTreatment` mapping, so a polymorphic
  Cryptol def that hits one of them surfaces as an unknown
  identifier at Lean elaboration. Long-term plan §6 keeps this
  deferred ("expand surface as case studies demand"); refactor to
  monomorphise away from class methods (`(==)` on a known type,
  `(+)` on `[N]`, …) until coverage lands.

## Documentation

Top-level docs are the **current** as-of-today reference:

- [`doc/architecture.md`](doc/architecture.md) — design overview.
- [`doc/getting-started.md`](doc/getting-started.md) — a 30-minute
  walkthrough from a Cryptol property to a closed Lean theorem.
- [`doc/contributing.md`](doc/contributing.md) — how to add a
  primitive, extend a soundness gate, write tests.
- [`doc/2026-05-02_residual-trust.md`](doc/2026-05-02_residual-trust.md)
  — the trust authority: auditor-facing index of inherited-trust
  assumptions, including the current axiom inventory (§1.3–1.4:
  exactly the two Vec↔BitVec round-trip axioms). The earlier
  user-facing trust summary
  (`doc/archive/2026-04-24_soundness-boundaries.md`) is the
  superseded May-era snapshot, kept as history.
- [`doc/2026-07-14_release-plan.md`](doc/2026-07-14_release-plan.md)
  — current plan-of-record: the 0.01 (coherence) / 0.02 (coverage)
  release plan. Earlier plans-of-record
  (`2026-05-05_long-term-plan.md` and the two Phase-organized
  May-02 plans) remain in `doc/archive/` as historical accounts of
  work shipped.

Two living records moved out of TODO.md (2026-07-17):
[`doc/audit-history.md`](doc/audit-history.md) and
[`doc/decision-log.md`](doc/decision-log.md).

Every other dated doc at `doc/` top level is a LIVE design, contract,
or census (position-callee calculus, obligation placement, OP-3
successor, replay design, fragment-semantics scoping, conformance
roadmap, coverage census, the 2026-07-21/23 soundness and fidelity
reviews). Historical audit reports, executed plans, and superseded
designs live in `doc/archive/` (swept 2026-07-17 and 2026-07-24),
including the executed release audit
([`doc/archive/2026-07-14_release-audit.md`](doc/archive/2026-07-14_release-audit.md))
and the frozen TODO buildout record
([`doc/archive/2026-07-24_todo-execution-record.md`](doc/archive/2026-07-24_todo-execution-record.md)).

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
│   └── CryptolToLean/        # named for parity with Rocq's CryptolToRocq;
│                             #   the library itself is SAWCore→Lean —
│                             #   standalone Cryptol translation is a non-goal
│       ├── SAWCoreVectors.lean         # Vec ≡ Vector
│       ├── SAWCoreBitvectors.lean      # bitvector n ≡ Vec n Bool
│       ├── SAWCorePreludeExtra.lean    # iteDep / ite wrappers (L-7)
│       ├── SAWCorePrimitives.lean      # axioms + inductives
│       ├── SAWCoreCtorOrder.lean       # constructor-order assertions
│       ├── SAWCoreBitvectors_proofs.lean  # bv lemma library
│       └── SAWCorePrelude_proofs.lean     # round-trip + Nat lemmas
├── replay/                   # factored trust kernel (lean-check-core.sh)
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
(`leanprover/lean4:v4.32.0`).

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
- `otherTests/saw-core-lean/` — data-only test categories driven by
  one orchestrator (`test.sh`, whose header comment is the
  authoritative taxonomy): `drivers/` and `workflows/` (SAW runs
  diffed against goldens, emitted Lean elaborated), `differential/`
  (true semantic conformance: SAW and Lean observations compared),
  `obligations/` (emitted contract-shape pins), `proofs/` and
  `support-lemmas/` (Lean discharges against emitted artifacts /
  support-library lemmas), `proof-gaps/` (honest inventory of
  undischargeable obligations), `negative/` (hand-rolled
  should-fail Lean probes), `saw-boundary/` (SAW rejection and
  boundary diagnostics), `stretch/` (manual stress probes).

CI runs all three on every push (`.github/workflows/ci.yml`).
