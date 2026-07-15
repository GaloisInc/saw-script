# saw-core-lean status

Last updated: 2026-07-15 (release 0.01 hardening + test-tree
restructure; `doc/2026-07-14_release-plan.md`)

## Purpose

`saw-core-lean` is a SAW proof backend. Its job is to translate SAWCore
terms, Cryptol-module definitions, and SAW proof obligations into Lean 4
source so Lean can discharge or check those obligations in its kernel.

Operationally, it fills the same slot as a solver backend in a SAW
workflow: SAW emits a verification condition, the backend presents that
condition to another trusted engine, and success means the obligation is
closed. The difference is that Lean checking is proof-kernel based, so
the emitted artifact should remain inspectable and replayable.

## Current Strategy

The active design is Phase beta, implemented by the position/callee
calculus (`doc/2026-07-02_position-callee-calculus.md`): value-domain
SAW expressions translate to Lean expressions at `Except String T`,
where `T` is the Lean translation of the SAW type; type-level
expressions translate raw. As of the position-directed translation
refactor (`doc/archive/2026-07-08_position-directed-translation-plan.md`,
Slices 0–7 complete), the calculus IS the implementation:

- Every translation is directed by a declared expected position
  (`ExpectedPosition`); callees carry declared argument-mode
  conventions (`ArgMode` tables); adaptation between representations
  happens at a single chokepoint (`adaptTo`) where forbidden
  adaptations are unrepresentable.
- Producers stamp `TranslatedTerm` production records (the produced
  shape); records are the translator's single source of truth, and
  demanded positions flow through explicit parameters/conventions
  rather than stored stamps (the write-only produced-at stamp was
  removed by the 2026-07-14 release audit). Shape is never re-derived
  from emitted Lean terms — that inspection class is deleted and a
  source lint in the smoketest keeps it deleted.
- Equality subjects classify by the operand-domain rule
  (`standaloneEqualitySubjectRep`); no surround declares a
  representation. `Eq.rec` transports run at a fully declared
  `EqRecConvention`.
- Recursors run at a declared `RecursorConvention` derived from the
  motive result position; every directly-emitted `@Foo.rec` carries a
  Lean-checked constructor-order assertion (`saw_ctor_order`), so a
  reordered Lean support inductive or a reordered SAWCore declaration
  fails the emitted file loudly.
- SAW `error` routes to `saw_throw_error`; `Prelude.fix` and partial
  operations route through proof-carrying obligations with
  Lean-checked evidence.
- `offline_lean` is EMISSION-ONLY (2026-07-14): it writes the goal
  file and returns `SolveUnknown`, so the goal stays unsolved on the
  SAW side and scripts wrap it in `fails`. SAW never claims a goal on
  the strength of an export. `offline_lean_replay` is registered but
  disabled (fails with a named diagnostic) until real SAW-side replay
  lands. Pinned by `saw-boundary/offline_lean_export_only` and
  `saw-boundary/offline_lean_replay_disabled`. The LLVM
  `verifyObligations` loop runs every condition's tactic before
  failing, so multi-obligation `llvm_verify` still emits all files.

## Known State

Passing (the standing fences):

- Lean support library: `lake build` green, including the
  `saw_ctor_order` positive/negative self-tests.
- `cabal test saw-core-lean-smoketest`: 57 tests, including the
  Slice 7 anti-regression source lint.
- `otherTests/saw-core-lean`: `make conformance` exit 0 — 195 rows
  (differential SAW-vs-Lean evaluation, obligation shape, pinned known
  gaps), with emitted artifacts elaborated. Tree restructured
  2026-07-15 (see otherTests/saw-core-lean/README.md): `workflows/`
  split out of `drivers/` for the end-to-end SAWScript rows;
  `shape/` renamed `attacks/`; the 17 legacy `drivers/conformance_*`
  litmus rows dispositioned (15 retired against named successors,
  2 unique residuals migrated as `differential/vector_zip_unequal`
  and `differential/nat_division_defined`).
- Emitted-Lean byte-diff oracle: `.snapshots/op2-baseline`, re-cut
  2026-07-15 after the full suite ran exit-0 on the release binary —
  `support/emitted-lean-snapshot.sh diff .snapshots/op2-baseline`
  clean at 303 artifacts (re-cut 2026-07-15 after the worked-example
  slate landed: seq-surgery and Z-n workflow artifacts added). (The earlier "1267" count was inflated by
  a scan bug that swallowed retired baselines' frozen copies —
  fixed: the scan now excludes `.snapshots/` wholesale. History: the
  stale op1-baseline's 32 diffs were per-hunk reviewed — all the
  expected OP-2 `atRuntimeCheckedM` migration — plus this release
  work's own reviewed footprint.)
- Driver + workflow rows (`bash test.sh` per-row,
  `lean-driver-test.sh`) green, including the ChaCha20 core verify
  workflow and the prelude auto-emit driver; full `make test` exit 0
  on the restructured tree (72 gaps in full-suite inventory scope).

Known-gap census (release 0.01 posture): 64 pinned `.known-gap`
rows in conformance scope (differential/obligations/saw-boundary —
tiers 2-3 below), plus the 7 `proof-gaps/` rows and the stretch
probe carried in the full-suite inventory (tier 1 lives there).
Three tiers:

1. **Sound-but-undischargeable** (the top documented limitation):
   the wrapped-fix recurrence class — running sum, popcount,
   rec_ones, stream_fibs, ChaCha20 iterate — emits obligations that
   elaborate but cannot be discharged (`saw_fix_unique_exists` is
   unsatisfiable for strict bodies). SAW never claims these goals;
   the OP-3 successor design is the 0.02 headline.
2. **Clean rejections** (named diagnostics, pinned boundary rows):
   Stream@core / Either@core comprehensions, direct recursors
   (Nat/Pos/Z/Bool/Accessible*), user datatypes, proof-primitive
   realization families, SMT-array/enum/polynomial surfaces,
   raw-position `error`, Prop-instantiated pair carriers.
3. **Workflow scope**: `offline_lean` is emission-only — SAW leaves
   punted goals unsolved and never claims them; SAW-side replay
   (`offline_lean_replay`) is registered but disabled until 0.02+.
   Remaining differential gaps are proof-support ergonomics
   (starter tactics not yet closing concrete-vector/rational facts)
   and SAW-simulator `Unimplemented` stubs, all pinned.

Known holes, all loud or pinned:

- RESOLVED 2026-07-14 (release 0.01 decision): the former deliberate
  red pair `drivers/cryptol_chacha20_{core_iterate,iround_zero}` is
  reclassified to `saw-boundary/` as expected rejections pinning the
  named `Prelude::Stream@core` diagnostic (success goldens retired to
  git history). The translation path folds into the OP-3 successor
  design. The driver suite has no deliberately-red rows anymore.
- Direct recursors for Nat/Pos/Z/Bool/AccessibleNat/AccessiblePos are
  gated with specific diagnostics (constructor order / representation
  mismatches); the design for lifting the gate is
  `doc/2026-07-03_direct-recursor-semantics-design.md` (PosRep
  inductive + source-shaped checked realizations), tracked separately.
- User-datatype recursors and datatype auto-emission reject with
  diagnostics (pinned by `saw-boundary/user_datatype_rejection`).
- RESOLVED 2026-07-14 (both formerly-filed loud gaps): top-level
  `write_lean_term` annotates from the produced body's production
  record (pinned `obligations/write_term_runtime_nat`); pair carriers
  at a Prop component reject with a named diagnostic (pinned
  `saw-boundary/pair_prop_component_rejection`).
- RESOLVED 2026-07-14 (audited,
  `doc/2026-07-14_reachable-raw-error-disposition.md`): the
  `h_raw_error_ : False` contract is retired. Function-typed
  `Prelude.error` with a value-domain result lowers to the
  constant-error function (message preserved; polynomial t1 now
  elaborates sorry-free); all other raw-position error rejects with
  a named diagnostic (pinned `saw-boundary/raw_error_rejection`).
- Filed 2026-07-12 (TODO.md, design gap): `saw_fix_unique_exists` is
  unsatisfiable for every strict wrapped fix body — errors are always
  fixed points of eager `Except` bodies, so the recurrence-class
  examples (running sum, popcount, rec_ones, stream_fibs, ChaCha20
  iterate) emit obligations that elaborate but can never be discharged.
  Sound but unusable; needs a contract revision design doc.
- RESOLVED 2026-07-12 by Slice OP-2 (was: eta-expanded checked-access
  wrappers fabricated unprovable `η < n` evidence): evidence-less
  positions now route through `atRuntimeCheckedM`, and the
  saw-lean-example invol/eq_spec goals discharge.
- Shipped 2026-07-12 (Slice OP-1): emitted evidence chains gained the
  checked `assumption | omega | normalize; omega` step (plus `rfl` for
  unsafeAssert and the div/mod bridging lemmas); nine differential
  known-gap rows un-gapped into true coverage (census 77→68). The
  surviving `sorry`-pinned rows expose two named surfaces for OP-2:
  guard-dependent `iteM (ltNat i k)` branch bounds emitted without the
  guard as evidence, and value-dependent bounds over runtime Nats
  (details in the design doc's OP-1 implementation record).
- Shipped 2026-07-12 (Slice OP-2, second Opus audit folded in):
  evidence-less `at` positions lower through `atRuntimeCheckedM`
  (Prelude-exact error semantics) decided by interval entailment over
  the binder bounds environment; interval-entailed slots keep the
  proof-carrying form. Four more rows un-gapped (census 68→64), and
  the saw-lean-example invol/eq_spec goals now discharge end-to-end
  from raw emitted artifacts — the eta-wrapper hole is closed.
- Filed 2026-07-12 (pinned `saw-boundary/polymorphic_seq_module_rejection`):
  whole-module translation of polymorphic indexing comprehensions
  rejects at `Prelude::Either@core` — same recursor-convention hole as
  the parked Stream@core pair; blocks the saw-lean-example
  `write_lean_cryptol_module` step.
- Two Vec/BitVec round-trip axioms remain in the support library TCB
  (cheap, separately tracked proof task).

## Next Work

Release 0.01 posture (`doc/2026-07-14_release-plan.md`): the
remaining items below are 0.02+ coverage work, shipped in 0.01 as
documented limitations or pinned rejections.

1. Slice OP-3 (obligation-placement program,
   `doc/2026-07-12_obligation-placement-design.md`): successor design
   against the third audit's six minimum conditions, then a fourth
   audit — acceptance is `proof-gaps/cryptol_running_sum_verify`
   closing end-to-end. The Stream@core / Either@core
   recursor-convention translation paths (now pinned expected
   rejections) fold into this design.
2. The direct-recursor / `PosRep` program
   (`doc/2026-07-03_direct-recursor-semantics-design.md`) — now
   tractable on the position-driven recursor convention.
3. SAW-side `offline_lean_replay` (the command is registered and
   disabled; the semantics are already scoped in the docs).
4. Universe-generalized pair/record carriers (would lift the
   pair-at-Prop rejection), proof-primitive realization families,
   user datatypes — example-driven coverage.
