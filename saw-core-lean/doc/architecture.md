# saw-core-lean: architecture (as of 2026-07-14)

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
`2026-05-02_residual-trust.md`).

Three SAWScript primitives drive the backend:

- `write_lean_term : String -> [(String, String)] -> [String] ->
  String -> Term -> TopLevel ()` — emit one term as a `def`.
- `write_lean_cryptol_module : String -> String ->
  [(String, String)] -> [String] -> TopLevel ()` — emit a whole
  `.cry` file as a Lean `namespace` block of `def`s.
- `offline_lean : String -> ProofScript ()` — emit a SAW proof
  obligation as a `def goal : Prop := ...; theorem goal_holds : goal
  := by sorry` stub the user discharges. EMISSION-ONLY: the goal is
  left unsolved on the SAW side (wrap in `fails` to continue a
  script); SAW never claims a goal on the strength of an export.
- `offline_lean_replay : String -> ProofScript ()` — the SAW-side
  DISCHARGE path (landed 2026-07-16): re-emits the goal fresh
  in-process (the authority), kernel-checks the user's completed
  proof against it under the factored trust kernel
  (`saw-core-lean/replay/lean-check-core.sh` — exact-match axiom
  allowlist, placeholder policy, drift check, source lint), and
  admits the goal only on success, recording `LeanReplayEvidence`.
  Assets resolve relocatably (Cabal data-files + cache staging,
  2026-07-23); `SAW_LEAN_ROOT` is an optional dev/CI override.

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

## Minimal backend emission

The Haskell backend is deliberately not a prover. Its job is to emit
the smallest faithful Lean representation of the SAWCore term plus any
explicit contracts needed for soundness. It should be simple enough to
audit by inspection:

- construct Lean syntax, names, binders, imports, and explicit
  contract propositions;
- preserve SAWCore control flow and value/error behavior;
- reject unsupported shapes before emitting a semantically different
  Lean term;
- leave missing evidence as a visible obligation.

The backend should not normalize generated Lean terms, classify
semantic patterns, discharge arithmetic, erase preconditions, or add
fallback lowerings because they make examples elaborate. Any nontrivial
reasoning belongs in Lean: as a checked helper type, theorem, proof
term, or user-support tactic. Convenience automation may live in the
Lean proof-support library, but generated backend output must not rely
on broad Haskell-selected proof search to count as correct emission.

## Module map

```
saw-core-lean/
├── doc/
│   ├── architecture.md       (this file — current reference)
│   ├── getting-started.md    (Phase 2 walkthrough)
│   ├── contributing.md       (how to extend)
│   ├── 2026-05-02_residual-trust.md         (trust authority + axiom inventory)
│   ├── 2026-07-02_position-callee-calculus.md (canonical translation contract)
│   ├── 2026-07-14_release-plan.md           (current plan-of-record)
│   └── archive/              (dated trajectory docs + concluded plans/audits)
├── lean/CryptolToLean/       (handwritten Lean support library)
│   ├── SAWCorePrimitives.lean         (primitive realizations: bv ops, Either, …)
│   ├── SAWCorePreludeExtra.lean       (iteDep / ite wrappers, streamScanl)
│   ├── SAWCoreVectors.lean            (Vec n α := Vector α n alias)
│   ├── SAWCoreBitvectors.lean         (bv-Vec aliases)
│   ├── SAWCoreBitvectors_proofs.lean  (bv identity THEOREMS — zero axioms)
│   ├── SAWCorePrelude_proofs.lean     (addNat/gen/foldr lemmas — zero axioms)
│   └── SAWCoreCtorOrder.lean          (saw_ctor_order assertion command)
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
- `otherTests/saw-core-lean/{negative,saw-boundary,proofs}/` —
  bespoke per-test directories: `negative/` (hand-rolled shouldfail
  probes) and `saw-boundary/` (rejection/boundary litmuses,
  including the lockdown gate-firing tests), `proofs/` for
  end-to-end proof discharge (see
  `otherTests/saw-core-lean/README.md` for the full category
  taxonomy).

## Soundness boundaries

The trust authority is `2026-05-02_residual-trust.md` (the May-era
user-facing summary is archived at
`archive/2026-04-24_soundness-boundaries.md`). Quick summary:

- **Translator-time refusals**: `polymorphismResidual` (sort k>0
  binders), `UnsoundRecursor` (Nat/Pos/Z/AccessibleNat/AccessiblePos
  `#rec` survivors), `RejectedPrimitive` (`fix_unfold` and other
  primitives with no proof-carrying interface),
  `scNormalize` 100-iter cap. Each pinned by a regression test.
- **Proof-carrying `Prelude.fix`** (two-state since R4,
  2026-07-16): a WRAPPED (value-domain) fix either matches a
  recognized productive class and lowers to a PROVEN realization —
  Class F bounded-lookback recurrences via `saw_fix_bounded_choose`
  under the per-instance proven obligation
  `saw_fix_bounded_productive`, Class S single-step stream
  corecursion via `saw_stream_realize` under
  `saw_stream_single_productive` — or REJECTS with a named
  diagnostic carrying the recognizer's reason. The wrapped
  unique-fixed-point contract (`saw_fix_unique_exists`) is RETIRED
  and no emitter may produce it (the driver harness's
  obsolete-helper scan enforces this). Raw-position fixes
  (function/proof/index results) keep the raw proof-carrying
  contract `saw_fix_unique_exists_raw`.
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

For regression tests that use a user-completed generated outline, the
completed file is not allowed to become a new source of truth. The proof
harness imports the tracked generated artifact under a private namespace
and requires the completed `goal` to be definitionally equal to the
generated `goal` by `rfl`. This accepts harmless Lean-normal forms such
as numeric macro reduction, but it rejects hidden semantic rewrites; any
non-definitional bridge must be a separate Lean-checked proof.

See `getting-started.md` for a complete walkthrough.

## Strategic next steps

The plan-of-record (`2026-07-14_release-plan.md`: 0.01 coherence,
0.02 coverage) defines the strategic posture:

- **Recursion**: `Prelude.fix` is a proof-carrying surface. The
  backend emits generic fixed-point obligations and leaves recurrence
  simplification to Lean-checked proof libraries; the recurrence
  class ships in 0.01 as the documented top limitation (OP-3
  successor design pending). Full SHA-512 is retained as a stretch
  scalability probe (`stretch/sha512_full_module_probe/`), not as a
  parity blocker. `fix_unfold` still rejects as a raw primitive.
- **Coverage expansion (0.02)**: example-driven — fill in primitives
  and conventions as demos surface. Historical coverage inventory:
  `doc/archive/2026-05-06_cryptol-coverage-gaps.md`; current
  inventory: `otherTests/saw-core-lean/CONFORMANCE.md`.
- **Proof-side tooling**: the support library ships checked lemmas;
  broader tactic ergonomics remain a later layer
  (`doc/proof-cookbook.md` documents the manual recipes).

The `Lean.BitVec` binding LANDED (Phase 9): every `bv*` operation is
a `noncomputable def` routing through native `BitVec` via the
`vecToBitVec`/`bitVecToVec` round trip, and the former bv axioms are
proven theorems. The trusted base is the two round-trip axioms
(`SAWCorePrimitives.lean`), tracked as a separately-provable TCB
item.
