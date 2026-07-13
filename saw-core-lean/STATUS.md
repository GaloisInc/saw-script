# saw-core-lean status

Last updated: 2026-07-12

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
refactor (`doc/2026-07-08_position-directed-translation-plan.md`,
Slices 0–7 complete), the calculus IS the implementation:

- Every translation is directed by a declared expected position
  (`ExpectedPosition`); callees carry declared argument-mode
  conventions (`ArgMode` tables); adaptation between representations
  happens at a single chokepoint (`adaptTo`) where forbidden
  adaptations are unrepresentable.
- Producers stamp `TranslatedTermAt` production records (shape +
  position); records are the translator's single source of truth.
  Shape is never re-derived from emitted Lean terms — that inspection
  class is deleted and a source lint in the smoketest keeps it deleted.
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

## Known State

Passing (the standing fences):

- Lean support library: `lake build` green, including the
  `saw_ctor_order` positive/negative self-tests.
- `cabal test saw-core-lean-smoketest`: 57 tests, including the
  Slice 7 anti-regression source lint.
- `otherTests/saw-core-lean`: `make conformance` exit 0 — 193 rows
  (differential SAW-vs-Lean evaluation, obligation shape, pinned known
  gaps), with emitted artifacts elaborated.
- Emitted-Lean byte-diff oracle: baseline re-cut 2026-07-12 after the
  Slice OP-1 evidence-chain refresh —
  `support/emitted-lean-snapshot.sh diff .snapshots/op1-baseline`
  clean at 634 artifacts (the slice0 baseline is superseded).
- Driver rows (`bash test.sh` per-driver, `lean-driver-test.sh`) green,
  including the ChaCha20 core verify and prelude auto-emit drivers.

Known holes, all loud or pinned:

- One deliberate red pair: `drivers/cryptol_chacha20_{core_iterate,
  iround_zero}` (`Prelude::Stream@core` rejection vs goldens expecting
  success) — parked pending a user decision between the
  parametric-bridge translation path and an expected-rejection
  category. Do not refresh those goldens.
- Direct recursors for Nat/Pos/Z/Bool/AccessibleNat/AccessiblePos are
  gated with specific diagnostics (constructor order / representation
  mismatches); the design for lifting the gate is
  `doc/2026-07-03_direct-recursor-semantics-design.md` (PosRep
  inductive + source-shaped checked realizations), tracked separately.
- User-datatype recursors and datatype auto-emission reject with
  diagnostics (pinned by `saw-boundary/user_datatype_rejection`).
- Filed pre-existing gaps (TODO.md): top-level `write_lean_term` of a
  runtime-computed Nat annotates a raw `: Nat` against a wrapped body;
  `PairValue` at a Prop instantiation emits a carrier the
  `PairType : Type -> Type -> Type` realization cannot take. Both fail
  loudly at elaboration.
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

1. Slice OP-3 (obligation-placement program,
   `doc/2026-07-12_obligation-placement-design.md`): productivity-gated
   wrapped-fix revision — acceptance is
   `proof-gaps/cryptol_running_sum_verify` closing end-to-end. Plus
   the OP-2 follow-up design decision on reachable raw `error`
   disposition (TODO.md).
2. The direct-recursor / `PosRep` program
   (`doc/2026-07-03_direct-recursor-semantics-design.md`) — now
   tractable on the position-driven recursor convention.
3. The two filed emission gaps above (both have clear fixes: annotate
   from the produced record's shape; reject or universe-generalize the
   Prop-instantiated pair).
4. Resolve the parked Stream@core pair decision.
5. SAW-side `offline_lean` replay plumbing (deferred by design).
