# SAWCore Lean Backend Roadmap

This is the working roadmap for bringing the SAW Lean backend to a sound,
usable state. Detailed design notes live in `doc/`; this file tracks the
current execution order and decision points.

## Goal

Mirror the Rocq backend's user-visible feature surface in Lean while preserving
the SAWCore semantics exactly. This includes Lean proof-obligation discharge
analogous to `offline_rocq`, direct term emission analogous to
`write_rocq_term`, support-library regeneration analogous to the Rocq prelude
emitters, and whole-Cryptol-module extraction analogous to
`write_rocq_cryptol_module`.

Hard requirements:

- Never erase or reinterpret `Except.error`.
- Reject unsupported SAWCore shapes before emitting semantically different
  Lean.
- Finished backend users may need to prove emitted Lean obligations, but they
  must not need to change the Haskell emitter or Lean generation for in-scope
  SAWCore terms. A new example that requires emission changes is a backend
  coverage bug unless it hits a documented final boundary or upstream language
  extension.
- Keep the Haskell backend as small and auditable as possible. It emits
  faithful Lean syntax and explicit contracts; it does not prove, normalize,
  simplify, classify semantic equivalences, or make examples pass by adding
  backend-selected automation.
- Treat every Haskell-side "clever equivalence" recognizer or rewrite as
  removal-target code. The acceptable replacement is proof-carrying emission:
  emit the literal obligation plus optional Lean-side checked helpers/lemmas.
- Do not add unjustified Lean axioms or widen the trusted base.
- Do not accept proofs that depend on proof-local native-evaluation axioms.
- Prefer deterministic wrapping decisions over emitted-Lean pattern matching.
- Keep tests and goldens aligned with Lean elaboration, not just textual output.
- Do not treat Rocq feature parity as permission to emit unsound Lean; parity
  gaps must reject cleanly until they can be implemented with a defensible
  contract.

## Rocq Parity Surface

The intended public surface mirrors the Rocq backend commands, modulo legacy
`coq` aliases:

- `write_lean_term` mirrors `write_rocq_term`.
- `write_lean_cryptol_module` mirrors `write_rocq_cryptol_module`; this is an
  in-scope feature, not a legacy path to disable.
- `write_lean_sawcore_prelude` mirrors `write_rocq_sawcore_prelude`.
- `write_lean_cryptol_primitives_for_sawcore` mirrors
  `write_rocq_cryptol_primitives_for_sawcore`.
- `offline_lean` mirrors `offline_rocq`.

Proof discharge is the primary verification workflow, but the whole backend goal
is Rocq feature parity with Lean's kernel as the checker.

Working matrix: `doc/archive/2026-06-26_rocq-parity-matrix.md`.

## Proof Discharge Workflow

The target backend workflow is two-phase. Lean proof construction does not need
to be fully automated:

1. SAW emits an exact Lean proof obligation for the current verification goal.
   The emitted file may contain a proof stub and should be stable enough for a
   human, tactic, or AI assistant to work against.
2. A user or automation writes/repairs a Lean proof in a separate proof file.
3. SAW later checks the completed proof by invoking the pinned Lean toolchain
   on the exact emitted obligation and proof file. SAW may accept the original
   goal only if Lean kernel-checks a theorem whose type is that obligation, with
   no forbidden escape hatches such as `sorry`, unchecked user axioms, import
   shadowing, or a proof of an unrelated proposition.

This is still proof discharge, even when step 2 is manual or AI-assisted. The
critical soundness boundary for the final backend is the check step, not
automatic proof search.

Lean automation policy for the current prototype:

- Automation belongs in the Lean user/proof-support library, not in the
  Haskell emitter. Generated proof outlines may expose placeholders and use
  evidence already present in context, but broad tactic search is a later
  proof-ergonomics layer.
- `grind`, `simp`, `omega`/`bv_omega`, `cbv`, and hand-written helper lemmas are
  acceptable when the checked theorem's axiom report contains only the allowed
  standard axioms plus the explicitly cataloged support-library assumptions.
- Plain `bv_decide` and `bv_check` are not acceptable in completed backend
  proofs today. Although they use an LRAT certificate and a verified checker,
  the current Lean frontend validates the certificate through native evaluation
  and inserts a proof-local native axiom for substantial goals. This widens the
  trusted base to Lean code generation, which is outside the backend's current
  soundness policy.
- Hard BV-heavy crypto obligations should remain explicit proof obligations,
  manual/checked proof-library work, or expected gaps. Lack of automated BV
  discharge is not a reason to weaken the emitted obligation.
- `bv_decide?` may still be useful as research input, but any cached proof path
  must be audited with `#print axioms` before it can become an accepted
  regression mechanism.

Near-term prototype priority is slightly different: we first need emitted Lean
obligations that are semantically correct, elaboration-stable, and realistically
provable. Several audit findings are "good-faith use of Lean" issues: a user can
edit a generated file to prove a different theorem or import extra axioms. Those
are real product soundness issues, but they are not the deepest technical blocker
for the prototype unless they let our regression tests falsely validate a broken
emission strategy. (The worst instance — `offline_lean` acting as an ADMITTING
exporter, claiming the goal on mere emission — was CLOSED 2026-07-14:
`offline_lean` is now emission-only, returning `SolveUnknown` so the goal stays
unsolved on the SAW side; `offline_lean_replay` landed as a real checker
2026-07-16 — fresh in-process emission is the authority, the factored
`lean-check-core.sh` trust kernel enforces the exact-match axiom allowlist,
sorry/placeholder policy, anti-trivialization and closer-type probes, and the
goal-telescope arity pin refuses emission on quantifier drift. Pinned by
`saw-boundary/offline_lean_export_only` (false goal must leave SAW unfinished
while still emitting), `workflows/replay_e1_verify` /
`replay_running_sum_verify` (positive), and
`saw-boundary/replay_reject_{sorry,axiom,suffix_axiom}` (negative). The LLVM
`verifyObligations` loop now runs every verification condition's tactic before
failing on unfinished proofs, so multi-obligation `llvm_verify` runs still emit
ALL obligation files in one pass.) Therefore:

- Prototype-critical harness checks should prevent stale artifacts, unrelated
  proofs, generated `sorry` dependencies, and unchecked axioms from making a
  regression look green.
- `offline_lean` remains emit-only (`SolveUnknown`; scripts wrap in `fails`):
  SAW never claims a goal on the strength of an unread export.
- `offline_lean_replay` (DONE 2026-07-16) is the discharge path: it re-emits
  the goal fresh in-process, stages the user's completed proof against that
  fresh emission (drift is load-bearing), runs the factored
  `lean-check-core.sh` trust kernel under a cleared `LEAN_PATH`, and only on
  full success returns `LeanReplayEvidence` (toolchain/goal-hash/proof-hash/
  axiom record; non-recheckable trust token, absorbing in verification
  summaries as `LeanReplayedTheorem`). Recorded hardening follow-ups: rebase
  the CI harness onto the same factored checker (single-checker by mechanism),
  and strengthen the goal-telescope pin from arity to binder-type comparison.

## Current State

The Phase-beta expected-shape migration is in place: `BindingShape` tracks
raw/wrapped/function bindings, result shapes are carried by translation paths
(not rediscovered from emitted Lean), the old result-shape classifier and
broadly-defaulting stream helpers are gone, and `fix`/`MkStream` lower through
generic proof-carrying obligations rather than Haskell-side productivity
assumptions. The auto-emitted SAWCore Prelude path has an explicit
raw-vs-wrapped declaration convention.

The 2026-07-02 position/callee work established the semantic contract
(`doc/2026-07-02_position-callee-calculus.md`); the position-directed
refactor that followed (Slices 0-7, COMPLETE 2026-07-11) closed the
bottom-up/top-down gap that work identified — the calculus IS the
implementation now (declared positions, declared conventions, single
adaptation chokepoint; see STATUS.md's Current Strategy).

The backend is not yet complete for arbitrary accepted SAWCore or the full Rocq
feature surface. The next priority is emission quality: every emitted Lean file
should either elaborate with explicit proof obligations or fail at SAW
translation with a clear, principled diagnostic.

The 2026-07-02/03 slices (raw-logical `Eq`/`Refl`/`Eq.rec`, raw/wrapped
recursor and dictionary convention, fold-family value-function convention,
direct-vector fallback review, prefix-partial checked-access) are landed and no
longer active blockers. Their design docs remain useful references:
`doc/archive/2026-07-02_raw-wrapped-recursor-dictionary-plan.md`,
`doc/archive/2026-07-03_higher-order-function-conventions-goal.md`,
`doc/archive/2026-07-03_higher-order-proof-carrying-wrappers-goal.md`.

The remaining pinned surfaces (stream/productivity, direct recursors, proof
primitives, large crypto/LLVM stress) are tracked in Priorities 1–5 below. The
detailed priority sections that follow preserve the 2026-07-01 audit's ordering
for reference, but the operative next work is the position-directed refactor
described in the section immediately below.

## Release Plan (2026-07-14)

Full plan: `doc/2026-07-14_release-plan.md`. Decisions recorded there
(user-confirmed 2026-07-14):

- **0.01 (coherence)**: ship the current sound fragment with all
  fences green on a clean checkout and docs literally true. The
  Stream@core pair reclassifies as expected rejection; OP-3 ships as
  the documented top limitation (sound-but-undischargeable);
  `offline_lean` is scoped as emit-stage evidence.
- **0.02 (coverage)**: example-driven — OP-3 successor design first,
  then Stream/Either recursor-convention work, direct recursors
  (PosRep), proof-primitive realizations.

0.01 workstreams and exit criteria live in the plan doc; the items
below track execution state as always.

- [x] **W1 rev.cry frontier — CLOSED 2026-07-19.** Every sub-item
  landed: rev.cry is a TRUE differential row, both chacha rows
  elaborate (residual = observer #reduce budget only), and the
  exception-hunt / domain-map residual lists are fully discharged.
  History below:
  - [DONE 2026-07-18] Under-applied partial ops lower to
    runtime-checked wrappers (design + audit:
    doc/2026-07-18_underapplied-partial-op-wrapper.md; 13 wrappers,
    zero obligations, throws at the excluded point).
  - [DONE 2026-07-18] REV residual: recursor post-scrutinee args
    made convention-aware (eta part 3b) — the Num.rec trailing
    function slot now routes through
    translateFunctionActualAtConvention;
    differential/cryptol_rev_module is a TRUE differential row
    (SAW and Lean observations match).
  - [DONE 2026-07-19] CHACHA transport work: the pinned failure was
    NOT a function-carrier congruence hole — the spine dump showed a
    TYPE-SUBJECT Eq__rec (sort carrier) mixing a forced-raw motive
    with ambient-translated subjects/branch. Closed by the
    MODE-UNIFORM type-subject convention (EqualitySubjectTypeImage /
    MotiveComputesTypeImage; design + SAFE-WITH-CONDITIONS audit in
    doc/2026-07-18_transport-carrier-design.md, 2026-07-19
    sections). chacha20 core now ELABORATES; the row's residual gap
    is observer #reduce budget (re-pinned, same family as
    iround_zero). autoEmitRaw combinators need NO per-name carrier
    conventions (parametric in their carriers); KNOWN LOUD RESIDUAL:
    arrow-FORMING named combinators (piCong family) state raw
    arrows — an ambient call feeding a T-consumer mismatches
    loudly; extend when a row pins it.
  - [DONE 2026-07-19] Distinctness invariant (audit C3): named
    backstop now in the calculus doc (§Raw Logical Callees,
    type-subject sub-case) with TWO smoketest pins (wrapExcept sole
    carrier; support library defines no Except-headed type alias).
  - [DONE 2026-07-18] Total raw-target primitives unapplied in
    dictionary fields (intNeg, natToInt): the eta-adaptation
    program (parts 1-3b: instantiation-derived conventions,
    translateFunctionActualAtConvention with the raw-formal gate,
    etaAdaptFromConv for alias-typed globals, honest
    BindingFunction stamps) closed all of these;
    differential/cryptol_rev_module green.
  - [DONE 2026-07-19] Exception-hunt residuals: wrappedHelper
    predicates reclassified as the DECLARED UseMapsToWrapped-
    callback convention — single per-class classifier
    (wrappedHelperTypeIsWrapped) naming the DNat deviation and its
    authority (support-library helper signatures); DVarRaw
    (Prop-kinded family formals) aligned to D (raw); documented in
    the calculus doc (§Proof Obligations And Checked Helpers).
  - [DONE 2026-07-19] Domain-map residuals: B-3 (DVarRaw labels
    role-reflecting: RawPropositionPosition) and B-4
    (piFunctionConvention.resultPos projects classifyDomain;
    recursorMotiveFunctionConvention carries the elimSort gate)
    landed; emission byte-identical, corpus-pinned. [C-nit DONE
    2026-07-18: wrapExcept sole-carrier lint.]
  - [DONE 2026-07-19] Function-carrier Eq.refl transport corner:
    resolved by the mode-uniform type-subject convention (see the
    CHACHA item above); both chacha rows now elaborate and pin only
    the observer #reduce budget.

- [ ] **Pre-release soundness audit (release gate, added 2026-07-17).**
  An aggressive end-to-end scrutiny pass over the whole trust chain
  before any release is called ready — assume the backend is wrong and
  try to demonstrate it. Non-implementer perspective required (fresh
  auditor context, not the implementing session). Scope, at minimum:
  - **False-theorem probes against replay**: try to get
    `offline_lean_replay` to accept an unsound proof — axiom
    introduction beyond the allowlist (prefix/suffix/namespace and
    unicode-lookalike name variants), `open`/notation shadowing of
    checked helpers, macro/elab tricks, Prop-level trivialization,
    proofs of a different-but-similar goal, stale-artifact and
    staging-path confusion, `LEAN_PATH`/toolchain substitution.
  - **Emission-seam probes**: recognizer/lowering seams (the six-bug
    under-approximation pattern), telescope pin residue (same-arity
    wrong-type binders), rawification and adaptation chokepoints,
    `InjectCodeDecl` policy, `scLiteralFold`, the two Vec/BitVec
    round-trip axioms.
  - **Harness-blindness probes**: can a regression go green while
    checking nothing (vacuous goldens, `fails`-wrapped rows that fail
    for the wrong reason, known-gap census masking a real failure)?
  - **Differential stress**: adversarially chosen SAWCore terms where
    SAW evaluation and emitted-Lean evaluation could plausibly
    diverge (boundary widths, zero divisors, empty vectors, deep
    nesting, shadowing, exotic-but-legal module shapes).
  - Every finding lands as a pinned regression row (or a documented
    reject) before release; the audit report is a doc/ artifact.

## Operative Priority: Obligation Placement & Satisfiability

Full design: `doc/2026-07-12_obligation-placement-design.md`.

This is the current top technical focus, set by the 2026-07-12
release-candidate assessment. The position-directed refactor made the
translator's representation decisions sound; the remaining defects all
live one layer up, in the proof-carrying obligation layer, and share one
root cause: **the backend embeds obligations at positions where they
cannot be proved.** Three instances, one principle:

1. Evidence chains for derivable side conditions are too weak — the
   emitted `(first | assumption | skip); all_goals sorry` cannot close
   derived-index or constant bounds that a checked
   normalize-then-`omega` step closes; 19 of the 39 differential known
   gaps pinned on exactly this `sorry`. [RESOLVED by Slice OP-1,
   2026-07-12: nine rows un-gapped; the survivors pin on
   guard-dependent / value-dependent bounds (→ OP-2 scope addition)
   or concrete-vector nonzero facts (→ parked crypto-BV policy).]
2. Eta-expanded checked-access wrappers fabricate evidence in-lambda
   (`fun (η : Nat) => let h : η < n := (by …); …`) — a universal claim
   that is false for general `Nat` and unprovable at that position.
3. `saw_fix_unique_exists` quantifies uniqueness over all `Except`
   values, but errors are always fixed points of strict bodies, so the
   contract is unsatisfiable for the entire recurrence class it exists
   to support (kernel-checked counterexample; see the 2026-07-12 entry
   under Priority 1).

Slices (each emitted-Lean-diff-reviewed and green before commit):

- [x] **Slice OP-1 (DONE 2026-07-12)** — checked evidence chains: taught
  `boundsProofScript`/`partialOpProofScript` the
  `assumption | omega | normalize; omega` step and the unsafeAssert
  script a `rfl` step; added the four `rfl` div/mod bridging lemmas
  (`divNat_eq_div` family — omega atomizes bare `Nat.div`/`Nat.mod`)
  to `SAWCorePrimitives.lean` and the simp set; corpus goldens
  refreshed (including the Slice-7 stale-binary catch-up, see design
  doc implementation record); NINE differential rows un-gapped into
  true coverage (census 77→68). Completed outlines in
  `proofs/{E4,E5,t6}` kept — the proof harness's staging scan is
  textual and the chain embeds a loud `sorry` fallback by design.
- [x] **Slice OP-2 (DONE 2026-07-12)** — evidence-less checked access:
  `atRuntimeCheckedM` (bare Prelude error string) + interval-entailment
  decision (`natBoundsEnv` in Γ, `lowerCheckedHelperArgsDecided` gated
  on the `at` contract identity) per the audited amendment. Eta
  formals, guard-dependent branch bounds, and value-dependent runtime
  bounds all lower runtime-checked; interval-entailed slots keep the
  proof-carrying form (OP-1's nine rows unchanged). FOUR more rows
  un-gapped (census 68→64: cryptol_bv_entrypoints,
  cryptol_ec_sequence_split, sequence_append_reverse,
  bitvector_order_width) with matching SAW/Lean differential
  observations; `cryptol_ec_at_oob_bounds` re-pinned to the new
  contract (out-of-bounds literal → runtime error, not a FALSE
  obligation); saw-lean-example invol AND eq_spec discharge end-to-end
  from raw artifacts. Binding conditions honored: at-contract only;
  Prelude-exact error string, nothing interpolated; decision attached
  to the `at` contract entry, never shared IndexArg machinery;
  interval set = omega-closable operations only (minNat/maxNat/
  var×var-mulNat unbounded per the audit witnesses).
- [x] **OP-2 follow-up: reachable raw `error` disposition — DESIGNED,
  ADVERSARIALLY AUDITED, AND IMPLEMENTED 2026-07-14**
  (`doc/2026-07-14_reachable-raw-error-disposition.md`, audit record
  inside). The audit sharpened the 2026-07-12 census in three ways:
  the real census was FOUR emitters, not one (polynomial t1 plus
  `obligations/raw_error_{nat,prop,function}`, whose pins live in
  expected.txt directives); the t1 TCInf handler is REACHABLE (def
  parameter scrutinee — eliminator case handlers count as reachable);
  and a third option beats reject-vs-keep-False where it applies.
  Implemented rules: (1) non-dependent Pi-typed error with a
  value-domain final result lowers to the CONSTANT-ERROR FUNCTION
  through the standard `saw_throw_error` route — SAW's own message
  preserved (the old False contract silently dropped it), no
  obligation, artifact completable (t1 golden refreshed, elaborates
  sorry-free); (2) all other raw-position error REJECTS with a named
  diagnostic (pinned by `saw-boundary/raw_error_rejection`, three
  probes; the old obligations rows retired); (3)
  `translateRawErrorObligation` DELETED — its remaining trigger is
  never produced and not decidable at the handler position
  (`rawErrorResultShape` stays; if0NatRaw/raw-fix consumers).
  Accepted limitation (from the audit): a genuinely-dead branch
  through a raw-result error now rejects the def where it previously
  emitted-with-sorry; nothing completable is lost.
- [ ] **Slice OP-3** — RELEASE POSTURE (2026-07-14): ships in 0.01 as the
  documented top limitation (sound-but-undischargeable; SAW never claims
  the goals); the successor design + fourth audit continue post-release
  (see `doc/2026-07-14_release-plan.md`). ENTRY DECISION (2026-07-12):
  STRUCTURAL-FIRST;
  first structural draft REFUTED by the third Opus audit
  (2026-07-12, `doc/archive/2026-07-12_op3-structural-fix-design.md` — kept
  as the rejected-candidate record). Key audit facts for the
  successor design: real normalized bodies reference the recursive
  vector through `at (zip … rec xs) idx` and the nested
  `at (gen K (\i'' -> …)) (i-1)` `#`-append shape (NOT bare
  `at rec j`); SAW's lazy `at (gen K g) j = g j` must be reproduced —
  any strict intermediate gen/zip build forces later-index references
  and errors on every productive element (kernel-checked); the
  recursive handle must be the full wrapped vector; `atWithDefault`
  defaults must be preserved (OP-2 condition 1); novel error strings
  violate OP-2 condition 2 outside the divergence region; rec_ones /
  stream_fibs are wrapped-contract Stream rows that hard-reject if
  the wrapped contract is deleted without a stream story, and
  ChaCha20-iterate is on the RAW fix path (not unblocked by any
  wrapped-only design). Candidate directions the audit left open:
  whole-vector bounded iteration (Kleene: `body^n` from a seed —
  revisit the May parametric bridges `saw_self_ref_comp_iterate` /
  `foldl_eq_natRec_atWithDefault`, fully proved and retired) with a
  lazy-selection faithfulness argument, or hand-realized recurrence
  combinators matched at the `zip`-comprehension level. Next concrete
  step: successor design draft against the audit's six minimum
  conditions, then a fourth audit, BEFORE touching Term.hs. Original
  post-audit contract analysis follows:
  wrapped-fix revision, POST-AUDIT SHAPE (the
  2026-07-12 Opus audit refuted the unconditional pure-uniqueness
  contract with the witness `fix Bool (\b -> ite b True True)`: unique
  pure fixed point `true`, SAW meaning divergent — see the design doc's
  audit record): a productivity recognizer gates the fix lowering;
  recognized bounded-vec-fold / stream-corec shapes lower structurally
  (preferred) or through the pure-uniqueness contract (sound UNDER the
  gate, resting on the documented Cryptol-productivity trust links);
  every unrecognized fix shape REJECTS with a named diagnostic and a
  litmus row (including the Bool witness verbatim). Acceptance test =
  `proof-gaps/cryptol_running_sum_verify` closes end-to-end.
- [x] **OP-2 rider (audit action) — DONE 2026-07-14, folded into the
  follow-up above** (the census found the one real position REACHABLE,
  so the disposition redesign below/above replaced the False contract
  entirely). Original text: verify every in-corpus
  `h_raw_error_ : False` position is genuinely unreachable-with-context;
  a REACHABLE raw `Prelude.error` must reject per the calculus rather
  than emit an undischargeable `False`.

## Operative Priority (COMPLETE 2026-07-11): Position-Directed Translation

Complete; the full slice-by-slice execution record moved to
`doc/archive/2026-07-11_position-directed-translation-record.md`
(2026-07-17 doc reorganization). The calculus it implemented is
`doc/2026-07-02_position-callee-calculus.md`; residual debts filed
as their own items in the priorities below.

## Priority 0: Test Harness Integrity

- [x] Track all files required by true differential tests.
  - Immediate audit finding: `otherTests/saw-core-lean/.gitignore` ignores
    `**/*.lean`, so most `differential/**/lean-observe.lean` files are ignored
    and absent from a clean checkout even though local conformance runs depend
    on them.
  - Unignore and track differential observers and any other required
    source-level Lean harness files. Generated emitted `.lean` artifacts should
    remain ignored unless they are intentional `.lean.good` goldens.
  - Add a preflight check that fails when a differential test directory has
    required source files that are ignored or untracked.
  - 2026-07-01 checkpoint: `differential/**/lean-observe.lean` is unignored,
    and the conformance orchestrator preflights required differential source
    files plus ignored-observer status before running the suite.

- [x] Ensure producer tests cannot pass with stale emitted Lean.
  - Before every SAW producer run, delete the exact emitted file named by
    `source.txt` and any non-golden emitted `.lean` files owned by that test.
  - This applies to `lean-differential-test.sh`,
    `lean-obligation-test.sh`, and driver tests.
  - A test should only inspect Lean artifacts created by the current SAW run,
    or tracked `.lean.good` files in tests that are explicitly golden-based.
  - 2026-07-01 checkpoint: differential and obligation harnesses delete the
    exact `source.txt` output before invoking SAW, after validating that the
    source path names a local generated `.lean` file. Driver tests delete all
    non-golden emitted `.lean` files before producer runs.

- [x] Bind proof replay and completed-outline tests to current emission.
  - Proof examples may still use tracked `.lean.good` artifacts as regression
    fixtures, but the harness should make drift from the current producer
    loud. If a proof is meant to validate current emission, it must stage the
    just-emitted artifact or depend on a freshly checked driver/golden step.
  - Keep the existing `sorryAx` and axiom-report checks; this item is about
    stale-source coupling, not final SAW-side proof replay.
  - 2026-07-01 checkpoint: when a current emitted file exists next to the
    tracked `.lean.good`, proof replay fails if those files differ. Standalone
    proof runs can still use the tracked golden when no current producer output
    is present.

- [x] Harden differential observers against fake comparisons.
  - The observer must import and inspect the emitted artifact itself, not
    reconstruct an equivalent term or print an expected constant.
  - Prefer a machine-readable observer declaration naming the emitted symbol,
    or generate a small wrapper around a declared observed term. At minimum,
    add a lint/preflight check that catches observers which import `Emitted`
    but never reference its declarations.
  - 2026-07-01 checkpoint: the differential harness requires every observer to
    import `Emitted` and reference the emitted observation convention
    (`Observed`/`Emitted.`) before it will accept `LEAN_OBSERVED` output. This
    is a pragmatic lint, not a full observer DSL.

- [x] Keep known gaps visibly distinct from parity.
  - The current 79 `.known-gap` entries are useful backlog markers, not green
    conformance.
  - Keep `make conformance` useful for development, but add a strict mode or
    summary failure mode that makes "no known gaps remain" a separate explicit
    milestone.
  - Expected-gap success means "the gap is pinned", not "the backend conforms".
  - 2026-07-01 checkpoint: `test.sh conformance-strict` and
    `SAW_LEAN_FAIL_ON_KNOWN_GAPS=1` fail the run if any known gaps remain, while
    normal development conformance still reports pinned gaps separately.

- [x] Tighten expected-failure boundary tests.
  - Tests marked `*.expect-fail` should require the expected failing stage or
    explicitly record why exit status is not meaningful.
  - Where possible, record and check exit status in addition to the diagnostic
    text so a rejection test cannot pass after SAW starts accepting the input.
  - 2026-07-01 checkpoint: driver/boundary tests now fail when a
    `*.expect-fail` case exits successfully. This exposed a stale
    `coerce_eq` rejection-boundary row; that row was removed from
    `saw-boundary/proof_primitive_rejection` because the real current failure
    is already pinned by `obligations/proof_coerce_eq`.

## Priority 1: Emission Soundness

- [x] Implement proof-carrying partial-operation contracts.
  - Design reference:
    `doc/archive/2026-06-30_partial-operation-obligations-plan.md`.
  - This is the current top backend priority. Direct partial operations must
    not emit unchecked total-looking Lean calls at zero divisors or zero
    denominators. They must emit visible preconditions and consume Lean-checked
    evidence.
  - Scope, in order:
    1. [x] Direct scalar Prelude operations:
       `divNat`, `modNat`, `divModNat`, `intDiv`, `intMod`, `ratio`,
       `rationalRecip`.
       2026-06-30 checkpoint: these now route through a shared
       `PartialOpContract` table, emit local `h_nonzero_obligation_` /
       `h_nonzero_` bindings, and call checked Lean helpers. Nat operations
       use raw preconditions; Int/Rational value-domain operations use
       wrapped `Except` preconditions so proof automation can reason about the
       emitted computation before monadic bind erases its expression shape. The
       seven corresponding obligation fixtures have been promoted from known
       gaps. `ecDiv`, `ecMod`, `ecFieldDiv`, and `ecRecip` also promote through
       the same scalar path after normalization.
       Remaining proof-ergonomics gap: rational executable differential cases
       are pinned known gaps where the emitted obligations are correct but the
       starter tactic does not yet prove all rational nonzero facts.
    2. [x] Direct bitvector Prelude operations:
       `bvUDiv`, `bvURem`, `bvSDiv`, `bvSRem`.
       2026-06-30 checkpoint: these now use the same `PartialOpContract`
       table with explicit helper argument modes: raw width argument, wrapped
       vector operands, named `bvNonzeroM` precondition, and checked Lean
       helpers. The four direct BV zero-divisor obligation fixtures have been
       promoted from known gaps. Nonzero executable BV division is pinned as a
       proof-ergonomics known gap because the emitted obligations are sound but
       the starter tactic does not yet prove concrete vector nonzero facts.
    3. [x] Cryptol.sawcore wrappers:
       `ecDiv`, `ecMod`, `ecFieldDiv`, and `ecRecip` are covered by scalar
       normalization. `ecSDiv` and `ecSMod` now stay opaque across
       normalization and route through a checked wrapper contract over
       `Cryptol.Num`; the Lean helper case-splits on `Num` and requires
       `ecSignedBVNonzeroM` evidence for the finite positive case. This avoids
       any Haskell rewrite from `ecSDiv (TCNum (Succ n))` to `bvSDiv n`.
       2026-06-30 audit follow-up: the finite positive helper branch now calls
       `bvSDiv_checkedM` / `bvSRem_checkedM` instead of reimplementing signed
       BV division/remainder directly, with `rfl` helper theorems pinning the
       finite-successor equations.
       Planning reference:
       `doc/archive/2026-06-30_priority-1-principled-emission-plan.md`.
  - Implementation rule: add a small data-driven partial-operation contract
    interface. Haskell may construct the operation-specific proposition and
    call a checked helper, but it must not inspect generated Lean syntax to
    prove nonzero-ness, erase the obligation, or choose a total fallback value.
  - Lean support-library helpers should be thin proof-taking wrappers around
    the existing operations. The proof argument may be computationally unused;
    its purpose is to put the soundness precondition into the checked type of
    the emitted result.
  - 2026-06-30 checkpoint: all direct `obligations/partial_*` and
    `obligations/cryptol_ec_*_zero` zero-divisor/zero-denominator fixtures are
    positive obligation-shape tests for fully applied operations. Under-applied
    or over-applied partial-operation identifiers now reject with a pinned
    `saw-boundary/partial_operation_obligations/under_applied_partial`
    diagnostic until a proof-carrying function-wrapper design exists.
    Remaining gaps in this area are proof ergonomics for executable replay of
    nonzero Rational/BV examples, not missing fully applied emission contracts.

- [ ] Implement proof-carrying bounds/index contracts.
  - Design reference:
    `doc/archive/2026-06-30_bounds-index-obligations-plan.md`.
  - This is the current top backend priority. Bounds-sensitive indexing and
    proof-carrying vector operations must not emit unchecked total-looking
    indexing, arbitrary defaults, or trusted SAW proof terms. They must emit
    visible Lean obligations such as `i < n` or `off + len <= n`, and the
    emitted result must consume Lean-checked evidence.
  - Scope, in order:
    1. [x] Rewrite/promote the with-proof vector obligation fixtures so they
       exercise fully applied operations, while preserving under-applied
       rejection as boundary coverage.
    2. [x] Add thin Lean checked helpers for `atWithProof`, `updWithProof`,
       `sliceWithProof`, `updSliceWithProof`, and `genWithProof` as needed.
       Helpers should delegate to faithful vector operations or carry Lean
       realization theorems; they must not duplicate semantics without proof.
    3. [x] Add a declarative checked-application contract path in Haskell.
       Haskell may construct propositions and wire proof variables, but must
       not prove bounds, inspect index arithmetic, trust source proof terms, or
       pattern-match current examples.
    4. [x] Promote `obligations/vector_at_with_proof`,
       `obligations/vector_upd_with_proof`,
       `obligations/vector_slice_with_proof`,
       `obligations/vector_upd_slice_with_proof`, and
       `obligations/vector_gen_with_proof` as the contract path covers each.
       `genWithProof` uses a proof-binder adapter that replaces SAW's
       `IsLtNat i n` source proof binder with Lean evidence `i < n` and passes
       that checked evidence to `genWithProof_checkedM`.
    5. [x] Route finite `Cryptol.ecAt` through the same discipline and promote
       `obligations/cryptol_ec_at_bounds`.
       The implementation keeps `Prelude.at` opaque during normalization and
       routes fully applied uses through the checked-application contract table.
       This is intentionally more general than an `ecAt` classifier: Haskell
       does not inspect Cryptol index branches, it only emits the precondition
       attached to the underlying SAWCore vector access.
    6. [x] Add or classify branch coverage for `ecAt` negative-index and
       infinite-stream behavior before claiming `ecAt` complete.
       `differential/cryptol_ec_at_infinite` compares SAW and Lean for the
       stream branch. Finite literal nonnegative and current negative-index
       replay are pinned in `differential/cryptol_ec_at_literal_branches` and
       `differential/cryptol_indexing` as proof-support gaps: they now expose
       visible `i < n` obligations and must not rely on generated backend
       automation to count as executable parity. `obligations/cryptol_ec_at_*`
       pins the positive and out-of-bounds finite obligation shapes.
    7. [x] Design and implement the next generated-sequence evidence convention.
       Preserving `Prelude.at` exposes real obligations inside `genM` and
       derived finite sequence helpers. Existing executable rows that used to
       hide this via `atWithDefault` are pinned known gaps rather than silent
       passes until they are genuinely discharged. The implemented convention
       routes `Prelude.gen` to `genWithBoundsM`, whose callback receives both
       the generated Nat index and Lean-checked `i < n` evidence supplied from
       `Fin n`. This promotes direct generated-index rows such as
       `differential/vector_gen_at` and `differential/cryptol_parmap`.
       Direct literal/index rows such as `differential/vector_literal`,
       `differential/vector_literal_edges`, and `differential/sequence_map_zip`
       remain pinned where executable replay still contains visible proof
       stubs.
    8. [ ] Improve Lean-side proof support for direct and derived bounds.
       Remaining known gaps need facts about direct constant bounds, transformed
       indices (`subNat`, offsets, reverse/split/update branches, nested
       transpose indices), and some nonzero arithmetic obligations such as
       executable `intDiv`/`intMod` with literal nonzero divisors. Keep these
       as visible failures until Lean proves them; do not add Haskell
       arithmetic classifiers. Automatic proof discharge is not the backend
       objective: it belongs in explicit Lean-side proof support, and tests
       must continue to distinguish checked conformance from pinned gaps.
    9. [ ] Reflect Boolean branch guards into proof-carrying bounds.
       Remaining generated-sequence known gaps include branches guarded by
       emitted Boolean tests such as `ltNat`; the generated Lean does not yet
       expose a corresponding Prop hypothesis to the branch body. Preserve
       these failures until a Lean-checked guard-reflection helper supplies
       the evidence. Do not add Haskell arithmetic or branch classifiers.
    10. [ ] Add proof-library realization checks for the checked vector helpers.
        The current helpers are intentionally small definitions over Lean
        `Vec`/`Vector` operations, but final soundness should still have
        explicit Lean theorems documenting that `atWithProof_checkedM`,
        `genWithProof_checkedM`, `updWithProof_checkedM`,
        `sliceWithProof_checkedM`, and `updSliceWithProof_checkedM` realize the
        corresponding SAWCore `*WithProof` semantics. This is proof-library
        assurance work, not permission to add backend automation.
  - Acceptance: the conformance matrix records every target row as
    `obligation`, `known gap`, or `boundary`; full validation passes; and no
    target path relies on Haskell-side bounds reasoning.
  - 2026-07-01 adversarial audit follow-up:
    1. [x] Strengthen obligation-shape fixtures so they pin the actual
       proposition over translated terms, not merely `LT.lt`/`LE.le` and helper
       names.
    2. [x] Add focused coverage for the finite negative-index `ecAt` branch
       showing that the current Cryptol.sawcore semantics index position zero.
    3. [x] Add a `genWithProof` fixture whose body consumes the proof evidence,
       so the proof-binder adapter is tested rather than only the unused-binder
       case.
    4. [x] Keep checked-helper realization theorems tracked as proof-library
       assurance work, and avoid claiming executable parity for those helpers
       before those theorems exist.

- [ ] Implement proof-primitive obligation contracts.
  - Design reference:
    `doc/2026-07-01_proof-primitive-obligations-plan.md`.
  - This is the next backend-emission target after the bounds/index checkpoint.
    SAWCore proof primitives and lemma axioms must not be translated as Lean
    axioms, trusted SAW proof terms, hidden Haskell rewrites, or old fallback
    primitive names. Each in-scope fully applied surface must emit an exact
    proof obligation or call a checked Lean theorem/helper whose type realizes
    the source primitive.
  - Scope, in order:
    1. [x] Survey `Prelude.sawcore` proof-like primitives/axioms and the
       `SpecialTreatment` rejection table, and make sure every distinct family
       is represented by a positive row, known-gap fixture, separate phase
       reference, or explicit final-boundary rationale.
       2026-07-01 checkpoint: added an explicit proof-primitive inventory to
       `otherTests/saw-core-lean/CONFORMANCE.md`, comparing the source
       Prelude entries, Rocq handling, current Lean fixtures, and intended
       trust strategy. Added known-gap obligation fixtures for missing
       representative families: `bvAddZeroR`, `bvEqToEqNat`,
       `bvultToIsLtNat`, `natCompareLe`, `eqNatAddComm`,
       `IsLeNat_SuccSucc`, `tail_gen`, `foldl_nil`, `bvNat_bvToNat`,
       `bvEq_refl`, `not_bvult_zero`, `IsLtNat_to_bvult`, and
       `ite_split_cong`.
    2. [x] Design a declarative proof-primitive contract path. Haskell may
       translate arguments, construct the exact proposition, bind local proof
       evidence, and call checked theorem realizations; it must not prove,
       simplify, classify, inspect generated Lean, or trust source proofs at a
       different proposition.
       2026-07-01 checkpoint: added a `ProofPrimitiveContract` table in the
       term translator. Contracts declare arity, raw/wrapped argument
       translation modes, the local proposition to bind, and how checked local
       evidence is consumed. The table currently covers assertion-style BV
       bounds and `equalNatToEqNat`; it is deliberately small and data-driven.
    3. [ ] Promote representative equality/Nat rows where the contract shape
       is clear: `uip`, `coerce__eq`, `equalNatToEqNat`, and `proveLeNat`.
       Use checked Lean theorems only when they are axiom-clean; otherwise emit
       exact obligations and keep proof-library work separate.
       2026-07-01 checkpoint: `uip` now emits the exact proof-equality result
       as a local obligation. `equalNatToEqNat` now emits a theorem-shaped
       local obligation from the translated raw Boolean-equality premise to
       translated Nat equality, then applies that local evidence to the source
       proof argument. The fixture consumes the result through `Eq__rec` so it
       tests proof evidence without papering over the separate `eqNat`
       Prelude-alias emission gap. `coerce__eq`, `proveLeNat`, and
       `natCompareLe` remain pinned known gaps.
    4. [x] Promote assertion-style BV bound rows such as
       `unsafeAssertBVULt` and `unsafeAssertBVULe` by emitting the comparison
       fact as a local obligation when the source assertion reaches the
       backend. Do not treat these assertions as unconditional theorems.
       2026-07-01 checkpoint: fully applied `unsafeAssertBVULt` and
       `unsafeAssertBVULe` now route through a small proof-primitive contract
       table. The backend emits the monadic comparison proposition over the
       translated bitvector operands and returns local Lean evidence for that
       exact proposition. No Lean automation, theorem assumption, or Haskell
       BV reasoning was added. Bare/under-applied assertion names remain
       rejection-boundary cases.
    5. [ ] Promote representative BV/vector lemma rows such as `bvEqToEq`,
       `bvAddZeroL`, `head_gen`, and `foldr_nil` only through exact
       obligations or checked realization theorems. Leave BV-heavy proof work
       as known gaps until Lean-side proof support exists.
       2026-07-19 checkpoint: the vector generator/fold axiom family
       (`head_gen`, `tail_gen`, `foldr_nil`, `foldl_nil`) now emits
       TYPE-IMAGE obligations — the obligation is exactly the ambient
       translation of the application's OWN instantiated statement, read
       off the term's type tag (obligation = T(prop) BY CONSTRUCTION;
       `lowerTypeImageObligation` + `typeImageObligationPrimitives`, no
       hand-mirrored emission shapes). Enablers landed with it: raw
       `head`/`tail` support definitions (mapsTo treatments — the
       value-position rejection is GONE; vector_primitive_rejection
       re-pinned to EmptyVec/scanl only) and the RAW-TWIN table
       (`rawLogicalTwin`: gen/foldr/foldl lower to their raw support
       definitions inside raw translation mode, where the wrapped-helper
       convention has no denotation). All four obligations rows are
       positive; bare/under-applied names keep their rejection boundary.
       2026-07-01 checkpoint: `bvEqToEq` now emits a theorem-shaped local
       obligation from the translated monadic `bvEq` proof premise to the
       translated wrapped vector equality, then applies that local evidence to
       the source proof argument. The fixture uses a proof binder rather than a
       concrete `Refl` so it tests the contract shape without depending on Lean
       reducing a closed bitvector equality proof.
       2026-07-01 checkpoint: `bvEq_refl` and `not_bvult_zero` now emit exact
       monadic bitvector-comparison obligations against `Bool.true` and
       `Bool.false`, respectively. This generalized the comparison helper over
       the expected Boolean literal without adding BV reasoning in Haskell.
       2026-07-01 checkpoint: `bvAddZeroL` and `bvAddZeroR` now emit exact
       wrapped equality obligations for the translated `bvAdd` expression
       against the translated vector operand. This remains proof-carrying
       emission only; the existing Lean `bvAdd_id_l` / `bvAdd_id_r` theorems
       are not invoked from Haskell.
       2026-07-01 checkpoint: `bvNat_bvToNat` now emits the exact nested
       wrapped equality obligation for the translated `bvToNat` result fed
       back through `bvNat`. The contract deliberately mirrors the backend's
       monadic emission shape rather than simplifying it by a monad law, so
       Haskell is only constructing the proposition that Lean must check.
       `IsLeNat_SuccSucc` remains a pinned known gap because a positive fixture
       needs the raw `IsLeNat` proof datatype surface itself to be emitted or
       imported first; that is separate Prelude proof-infrastructure work, not
       a reason to add ad hoc support in this row.
       `bvEqToEqNat` remains a pinned known gap: a direct proof-value fixture
       exposes the separate `eqNat` Prelude-alias rejection, while consuming
       the proof through `Eq__rec` exposes the existing raw/wrapped `bvToNat`
       Nat mismatch in proof positions. Do not paper over either issue with a
       special proof-primitive contract; this needs the surrounding
       proof/value-shape interface fixed first.
       2026-07-01 checkpoint: `eqNatAddComm` now emits an exact local
       `Eq Nat (addNat x y) (addNat y x)` obligation and the fixture consumes
       that proof through `Eq__rec`, avoiding the unrelated direct `eqNat`
       Prelude-alias gap.
       2026-07-01 checkpoint: the adjacent `eqNatAdd0`, `eqNatAddS`, and
       `addNat_assoc` Nat arithmetic lemmas now use the same exact-obligation
       path and have focused obligation-shape fixtures.
    6. [x] Add any missing representative fixtures discovered by the survey,
       such as `bvEqToEqNat`, `bvultToIsLtNat`, `natCompareLe`, or a second
       BV-add-zero row if it follows a distinct realization path.
  - Acceptance: conformance records every target as `obligation`, `known gap`,
    or `boundary`; positive rows inspect the emitted artifact for exact
    propositions/evidence consumers or checked realization calls; and no new
    Lean automation, Lean axioms, or Haskell semantic proof logic is added.

- [ ] Close the bitvector primitive conformance surface found in the
  2026-06-29 audit.
  - `bvLg2` now uses SAW's ceiling-log convention for nonzero inputs. Added
    paired SAW-vs-Lean conformance coverage for `bvLg2 0`, `1`, powers of two,
    and non-powers of two.
  - Added the first differential conformance driver/proof pair:
    `drivers/conformance_bitvector` proves defined concrete SAWCore bitvector
    facts with SAW's `w4` backend and emits the same term for Lean elaboration;
    `support-proofs/conformance_bitvector` checks the corresponding Lean support
    realizations.
  - Division/remainder/modulus by zero is not a green conformance case today.
    Although some `Prelude.sawcore` comments describe concrete results, SAW's
    active concrete and What4 paths treat those cases as undefined. The Lean
    backend must therefore emit explicit nonzero-divisor preconditions/proof
    obligations, or reject until it can do so; it must not silently pick total
    Lean values.
  - 2026-06-29 checkpoint: `drivers/conformance_zero_divisor_obligations` was
    added to the unified conformance suite as a regression probe for the
    missing zero-divisor contract, but the first Haskell implementation was
    stripped because it was an ad hoc per-primitive dispatch block. The backend
    is intentionally back in the broken state here: the test documents the
    required behavior, not a completed fix.
  - 2026-06-29 checkpoint: `divModNat`'s support-library result type now uses
    SAW's nested `PairType ... UnitType` tuple representation instead of Lean's
    native `Nat × Nat`.
  - Remaining work: follow the dedicated partial-operation plan above, then
    audit higher-level Cryptol operations that may hide these primitives.
  - Audit reference: `doc/archive/2026-06-29_comprehensive-audit.md`.

- [x] Close the `fix` productivity surface for emit-stage soundness.
  - Current lowering emits generic fixed-point obligations
    (`saw_fix_unique_exists` / `saw_fix_unique_exists_raw`) plus local proof
    placeholders; nested constructors such as `MkStream` emit their own
    pointwise contracts.
  - The Haskell backend does not need to prove productivity. It emits the exact
    Lean contract and makes the lowering depend on checked evidence.
  - Completed proof artifacts must not rely on a hidden Haskell-side assumption,
    a shape-specific Haskell recognizer, or an unresolved generated placeholder.
  - Later proof ergonomics question: decide whether local obligations should be
    lifted into top-level declarations with explicit dependency binders, or
    whether edit-in-place obligation files are acceptable for generated code that
    depends on surrounding locals.
  - 2026-06-28 checkpoint: strengthened the wrapped-value generic `fix`
    contract so uniqueness ranges over all `Except String α` fixed points, not
    just successful `Pure.pure` fixed points. This rules out a successful
    witness coexisting with an `Except.error` fixed point.
  - Design reference: `doc/archive/2026-06-26_proof-carrying-soundness-contracts.md`.

- [x] Ensure rawification never hides residual per-index effects.
  - The old `rawifyExceptToRaw` Lean-AST rewrite engine has been removed from
    Haskell rather than kept as a trusted gate.
  - Added smoke coverage where `Prelude.error` remains under an
    index-dependent direct stream or stream-corecursive `fix`; these now emit
    explicit Lean contracts (`saw_mkStream_total_exists` or
    `saw_fix_unique_exists`) rather than defaulting.
  - Cryptol `iterate` should stay on the generic obligation path; any
    recurrence-specific ergonomics belong in Lean-checked proof scripts.
  - Added driver-harness checks asserting obsolete helpers do not appear in
    emitted output:
    `mkStreamM`, `mkStreamFix*`, `mkStreamFixPair*`, `cryptolIterateM`,
    `genFix*`, `GenFix*`, `StreamBodyProductive`, `PairStream*`, and
    `saw_unreachable_default`.
  - Remaining work: add end-to-end Cryptol driver coverage for representative
    source programs on both `offline_lean` and `write_lean_cryptol_module`
    paths once the exact user-facing rejection wording is stable.

- [x] Reject unsupported raw/proof/type/function uses of `Prelude.error`.
  - `Prelude.error` is now gated by the same wrapped-value-domain predicate
    used for binder/result shape decisions.
  - Raw Nat/Num indices, types, propositions/proofs, and function results fail
    at SAW translation with a direct diagnostic instead of emitting an
    ill-shaped `Except` term and relying on Lean elaboration failure.

- [x] Design and implement initial proof obligations for raw-position Cryptol
  partiality.
  - Raw `Prelude.error` at Nat/index, type, proof, or function results now emits
    a local `False` obligation and produces the raw result through
    `False.elim`, rather than manufacturing a default or trying to use
    `Except.error` at a raw type.
  - Polynomial literals: SUPERSEDED 2026-07-14 by the audited raw-error
    disposition — the TCInf handler now lowers to a constant-error function
    (no obligation, sorry-free); raw-position error REJECTS. This item's
    False-obligation description is the retired mechanism (see
    `doc/2026-07-14_reachable-raw-error-disposition.md`).
  - Full SHA512 is no longer the acceptance criterion for this surface. It is a
    large stress probe for the same raw-error and proof-carrying-recursion
    contracts, and is tracked below as stretch scalability work.
  - Remaining ergonomics work: replace generic `False` obligations with more
    specific bounds/unreachable-branch propositions when the translator can
    state them cleanly.

- [ ] Track full SHA512 as a stretch/performance goal, not a Rocq-parity blocker.
  - Generic `Prelude.fix` fallback now emits `saw_fix_unique_exists`
    obligations for shapes outside the audited stream/vector lowerings.
  - Focused SHA residual probes can now emit large Lean files with explicit
    recursion/stream-totality obligations instead of failing at the first
    unsupported `fix`.
  - Full `write_lean_cryptol_module` for SHA512 is a very large stress test,
    not a feature required to match Rocq. Rocq rejects the analogous full-module
    path; Lean accepting focused proof-carrying terms is already beyond parity.
  - Optimization work such as sharing/top-level obligation factoring remains
    valuable, but it should be scheduled after the parity baseline is green and
    should be tracked as stretch scalability work.

- [x] Decide and implement the contract for `write_lean_sawcore_prelude`.
  - The auto-emit path walks SAWCore Prelude declarations directly through
    `SAWModule.translateDef`, not through the normalized Cryptol-user-term path.
  - The chosen convention is explicit:
    raw proof/type infrastructure auto-emits in `RawValueMode` over `Sort u`;
    wrapped value-domain facades either auto-emit into `Except String` or map
    to checked support-library declarations whose carrier binders live in
    `Type u`.
  - `sawLet`, `xor`, and `boolEq` map to small Lean support-library facades
    where direct SAWCore-body emission would mix raw callback arguments with
    wrapped value conventions.
  - Some proof-equation conveniences (`not__eq`, `and__eq`,
    `ite_eq_iteDep`) remain skipped until the proof-ergonomics phase decides
    whether they should be raw theorems, wrapped theorems, or hand-library
    lemmas.

- [x] Make the test status unambiguous.
  - `sawcore_prelude_auto_emit` now elaborates and has a refreshed golden for
    the generated `.prelude.lean` file.
  - The Lean elaboration harness now preserves diagnostics from failing
    `lake env lean` probes instead of exiting early under `set -e`.

## Priority 2: Emission Architecture

- [ ] Complete the audit-driven removal of clever/legacy emission paths.
  - 2026-06-28 audit reference:
    `doc/archive/2026-06-28_clever-legacy-path-audit.md`.
  - 2026-06-28 checkpoint: finished the `fix` migration cleanup. Deleted
    `FixShapes`, removed the dead `rawifyExceptToRaw` rewrite engine and
    dormant `MkStream` deferral switch, updated smoke tests to assert generic
    fixed-point and stream-totality obligations, and refreshed affected driver
    goldens.
  - Remaining audit targets are live or design-relevant clever paths:
    imported-name realization, numeric macro collapse/fallbacks, and residual
    raw/wrapped inference heuristics.
  - Continue removing backup or deferral switches that preserve old behavior
    whenever the proof-carrying path has become the only intended path.
    Old fallback behavior is not a compatibility feature for this backend: if
    it is not a faithful emission path, a documented rejection boundary, or a
    checked proof-carrying contract, it should be deleted rather than kept as a
    safety net.
  - Treat Haskell-side classifiers as valid only when they emit optional
    Lean-checked proof artifacts over the ordinary literal obligation. They
    must not erase, weaken, or replace the obligation.

- [ ] Ruthlessly delete fallback, backup, and legacy emission code.
  - Search the backend for fallback/legacy/backup language and old compatibility
    paths. For each one, either delete it, convert it to an explicit rejection
    boundary, or replace it with a faithful proof-carrying contract.
  - Do not preserve obsolete behavior to keep historical examples green. If an
    example depended on a legacy path, pin the resulting failure in the
    conformance or obligation corpus and fix the emission principle first.
  - Acceptance: there are no undocumented fallback paths in
    `SAWCoreLean.Term`, `SAWCoreLean.SpecialTreatment`,
    `SAWCoreLean.CryptolModule`, or the Lean support-library declarations that
    the Haskell emitter calls.

- [ ] Close semantics-injection paths in prelude/module emission.
  - 2026-06-28 checkpoint: removed generic `DefReplace` and moved the remaining
    `sawLet` / `xor` / `boolEq` facades into the Lean support library. Haskell
    now maps the SAW names to checked declarations instead of injecting
    verbatim Lean source.
  - 2026-06-28 checkpoint: generic `AxiomQualifier` / `PrimQualifier` emission
    now rejects by default in the module walker. Any remaining trust assumption
    must be an explicit support-library TCB entry, not reachable through
    ordinary preservation machinery.
  - 2026-06-28 checkpoint: imported constants no longer fall back to accidental
    bare Lean names. The translator emits an imported constant only when the
    user explicitly supplies a renaming or skip-list entry. Remaining work:
    make those explicit realizations carry audit-visible contracts connecting
    the Lean name to the SAW source meaning.
  - 2026-06-28 checkpoint: explicit imported realizations now emit an auxiliary
    `__saw_realizes_*` Lean alias at the translated SAW type, and generated
    terms use that alias instead of the raw external target. This makes the
    contract Lean-checked and audit-visible. Imported value/function constants
    also carry deterministic shape metadata so applications go through the same
    wrapper adaptation as local variables and ordinary translated globals.
    Remaining work: decide whether external realization declarations need a
    richer semantic proof obligation beyond type-correctness for the parity
    milestone, or whether that belongs in the later ergonomics/TCB phase.

- [ ] Remove or justify Haskell-side representation rewrites.
  - 2026-06-28 checkpoint: `NatPos` / `Bit0` / `Bit1` no longer collapse
    closed constructor chains in Haskell. They now emit one-to-one Lean helper
    calls (`natPos_macro`, `bit0_macro`, `bit1_macro`) and rely on Lean
    reduction when a concrete numeral is needed. Keep removing any remaining
    `UseMacro` uses that compute semantic equivalences rather than emitting
    syntax or wrapper plumbing.
  - 2026-06-28 checkpoint: `Zero` / `One` now follow the same helper pattern
    (`zero_macro`, `one_macro`) instead of emitting Lean numeric literals
    directly. The helpers are reducible and simp-normalizing, so proofs still
    reduce concrete lengths on the Lean side while Haskell stays syntactic.
  - 2026-06-29 checkpoint: `Succ` also routes through a reducible Lean helper
    (`succ_macro`) rather than a direct Haskell rewrite to Lean `Nat.succ`.
  - 2026-06-28 checkpoint: removed the global `liftRawValue` Lean-AST
    recognizer. All wrapped-formal adaptation now uses translated shape
    metadata or explicit `UseMapsToWrapped` conventions.
  - 2026-06-28 checkpoint: several wrapped-formal adaptation sites now use
    `TranslatedTerm` shape metadata instead of `liftRawValue` AST recognition
    (`if0Nat`, value-domain `Eq`, wrapped-helper conventions, array
    sequencing, top-level def wrapping, and Cryptol-module top-level
    wrapping). This also exposed and fixed a `Prelude.coerce` shape
    propagation gap.
  - 2026-06-28 checkpoint: `buildLifted` now consumes shaped translated
    arguments and wraps bind inputs from `BindingShape` metadata rather than
    inspecting Lean syntax.
  - Raw/wrapped inference remains transitional machinery. Continue migrating it
    toward explicit conventions and checked adapters; avoid adding new
    free-variable or Lean-AST heuristics.
  - 2026-06-29 audit finding: `scNormalizeForLean` still applies
    `scLiteralFold` in Haskell before Lean emission. Either remove this from
    trusted emission or make it proof-carrying by emitting the literal term plus
    a Lean-checked equality/obligation for the folded form.
  - 2026-06-29 experiment: a direct removal of `scLiteralFold` compiles after
    deleting dead code, but the Lean driver suite then emits many non-elaborating
    dependent vector terms. The breakage is not merely golden churn: unevaluated
    Nat/Int size arithmetic reaches casts, `coerce`, and vector helper lengths
    where Lean needs explicit equality evidence. Therefore this path needs a
    principled replacement, not a one-line deletion: emit literal arithmetic
    plus Lean-checked normalization/cast obligations, or make the relevant
    size-equality evidence explicit at each dependent use site.
  - 2026-06-29 checkpoint: moved `Prelude.Bit` from a direct Haskell replacement
    with Lean `Bool` into the Lean support library as a reducible `Bit` alias.
    Haskell now routes to that checked support declaration. This is a small
    instance of the general rule: representation choices belong in Lean-side
    realizations or proof-carrying contracts, not ad hoc Haskell rewrites.

- [x] Promote the design from scattered policy to explicit data types.
  - **COMPLETE (2026-07-11, via the position-directed refactor Slices
    1–6):** `ExpectedPosition` + `RawReason` (positions),
    `ArgMode`/`ResultMode` contract tables and `FunctionConvention` /
    `MotiveConvention` / `EqRecConvention` / `RecursorConvention`
    (callee conventions), and `TranslatedTermAt` production records
    (shape + produced-at position) are the shape abstractions.
    `CalleeConvention` was deliberately DELETED rather than filled in
    (Slice 4c): the dispatch's real classifier is the declarative guard
    chain over the contract tables. `BindingShape` remains the Γ-record
    representation (`BindingInfo` carries position and source type
    alongside it).
  - Original targets, for the record:
    - `ExpectedShape`
    - `RawReason`
    - `CalleeConvention`
    - richer `BindingShape` carrying relevant type/function information
  - Keep `BindingShape` as the binding environment, but stop using it as the
    only shape abstraction.
  - 2026-06-28 audit finding: the remaining shape gaps are no longer just
    readability issues. Non-application translations such as non-empty
    `ArrayValue` can produce wrapped Lean terms (`vecSequenceM`) while fallback
    shape inference classifies the term as raw. Under-applied wrapped helpers
    also override their explicit `UseArgRaw`/`UseArgWrapped`/`UseArgFunction`
    conventions. These are the next migration targets because they can make
    later adaptation reason from the wrong shape.
  - 2026-06-28 checkpoint: fixed these concrete migration gaps. Non-empty
    `ArrayValue` bindings keep wrapped shape, under-applied wrapped helpers
    adapt their supplied prefix through the explicit convention table, variable
    applications adapt from the translated Lean Pi shape, and recursor motives
    now use raw binders with wrapped value-producing results.
  - 2026-06-28 checkpoint: `UseRenameUniv` no longer has a backup path that
    silently drops explicit universes and asks Lean to infer them. The
    translator now derives levels from bound sort variables or from the
    argument's SAWCore sort (`Bool`/`Vec n Bool` -> level 1, `sort k` literals
    -> their next Lean sort), and rejects if a required level is still unknown.

- [x] Centralize adaptation.
  - **COMPLETE (2026-07-11):** `adaptTo` is the single adaptation
    chokepoint (Slice 2); positions are inputs (`translateAt`), so
    translation is position-directed rather than translate-then-repair;
    forbidden adaptations throw `ForbiddenAdaptation` — unrepresentable,
    never defaulted. The allowed/forbidden lists below are enforced by
    the chokepoint's type of allowed moves.
  - Target operation:
    - translate naturally and return a shape
    - adapt exactly once to an expected shape
  - Allowed adaptations:
    - raw value to wrapped value with `Pure.pure`
    - wrapped value to raw value only by binding in a continuation
    - raw type/index/proof to raw type/index/proof
    - function rawification only through named, precondition-checked adapters
  - Forbidden adaptations:
    - wrapped proof/type to raw proof/type
    - arbitrary `(a -> Except String b) -> (a -> b)`
    - defaulting on `Except.error`
  - 2026-06-29 audit finding: ordinary sort-literal translation may still use
    binder-position universe generalization where a value-position concrete
    sort literal is intended. Add focused tests before changing this path.

- [x] Replace transitional local policy.
  - **COMPLETE (2026-07-11, Slice 7 closing the refactor):**
    `shouldWrapBinder`, `isVariableHead`, `natValueResult`,
    `typeArgPositions`, and the `functionConvention*` predicates are
    documented CONVENTION-INTERNAL predicates consulted only by the
    convention derivations; the value-domain result rule is centralized
    in `phaseBetaResultIsValue` (single authority — application paths,
    partial-op contracts, eta expansion, the Pi body wrap, and the
    recursor motive convention all read it). `Eq`/`Eq.rec` run at the
    declared standalone-equality and `EqRecConvention` conventions
    (Slice 5); recursors at the declared `RecursorConvention`
    (Slice 6); `fix` and partial ops at proof-carrying contracts.
    `skipBinderWrap` / `inRecursorCaseBinder` survive as documented
    convention-scoped context flags, per the stated target ("not zero
    local cases"). The smoketest's Slice 7 anti-regression lint keeps
    the deleted heuristics deleted and caps the allow-listed
    emitted-type self-mirrors (`bindingShapeOfType`,
    `isExceptStringType`/`peelLeanPiTypes` in
    `applyKnownFunctionWithShape`) at their current consumer counts.
  - Original audit list, for the record:
    - `skipBinderWrap`
    - `inRecursorCaseBinder`
    - `shouldWrapBinder`
    - `typeArgPositions`
    - `natValueResult`
    - ad hoc special cases for `Eq`, `coerce`, `MkStream`, and `fix`
  - The target is not zero local cases; it is named conventions with explicit
    preconditions and regression tests.
  - The removed `FixShapes` classifier is the model for this migration: the
    preferred end state is generic proof-carrying emission plus Lean-side
    automation that proves the emitted contract for stream, vector, SHA-style,
    and other recurring patterns, not a better Haskell recognizer.
  - Shape recognition in Haskell is acceptable when it only emits additional
    Lean proof artifacts, such as a local lemma specialized to the generated
    body. The regular obligation must still be present, and final acceptance
    must depend on Lean checking the emitted lemma/proof.
  - Preferred proof-obligation shape: Haskell emits the literal/dumb contract
    needed by the checked helper, plus an optional Lean-side proof attempt that
    rewrites it into an ergonomic proof-library lemma. Failure of that proof
    attempt leaves the original obligation visible; it must not cause Haskell
    to erase, weaken, or reinterpret the contract.
  - 2026-06-28 checkpoint: `unsafeAssert` now follows this obligation-first
    rule. Fully-applied uses emit the asserted `Eq` proposition as a named local
    proof obligation; Haskell no longer drops the SAW arguments and replaces the
    call with a hidden tactic-only proof. The `saw_unsafeAssert` tactic remains
    available as Lean-side automation a user/proof script can apply to that
    visible obligation.
  - 2026-06-28 audit finding: `classifyPolyStreamIterate` violates this rule.
    It recognizes only a broad polymorphic-stream outer shape, discards the
    actual `fix` body, and emits `cryptolIterate α f x`. That is not obviously
    correct Haskell emission. It should be removed or demoted to optional
    Lean-proof generation over a regular emitted obligation; until then, the
    conservative behavior is to reject/fall back rather than rewrite.
  - 2026-06-28 checkpoint: removed `classifyPolyStreamIterate` and the
    `lowerPolyStreamIterate` Haskell rewrite. Higher-arity `Prelude.fix`
    applications now emit the generic fixed-point obligation for `fix type body`
    and apply the extra arguments normally, so Cryptol `iterate` coverage is
    retained without a Haskell-side semantic shortcut.
  - 2026-06-28 checkpoint: removed `rawifyExceptToRaw`, the broad Haskell-side
    Lean AST rewrite engine for `Except`-to-raw adaptation. Future adaptation
    work should use named adapters/contracts whose semantic preservation is
    checked in Lean.
  - 2026-06-28 checkpoint: deleted the old direct fix-shape Lean helper
    surface. Future recurrence ergonomics must prove facts about the generic
    emitted obligation rather than rewriting through a structural helper API.

- [x] Make `UseMapsToWrapped` more explicit.
  - `UseMapsToWrapped` now records per-formal conventions
    (`UseArgRaw`, `UseArgWrapped`, `UseArgFunction`) instead of only arity and
    target name.
  - Wrapped helper calls no longer reconstruct which arguments to lift from
    SAW binder syntax. The use-site table declares that policy directly for
    `genM`, `atWithDefaultM`, `foldrM`, and `foldlM`.
  - Result shape is explicit in the use-site constructor: these helpers return
    wrapped values. If a future helper needs a different result shape, it should
    use a different convention rather than reintroducing syntactic inference.
  - 2026-06-28 audit finding: the fully-applied path uses this table, but the
    under-applied path still applies supplied arguments directly. Fix this by
    adapting every supplied prefix with the same convention before returning a
    function-shaped partial application.

- [ ] Improve generated Lean readability where it does not affect semantics.
  - Reduce unnecessary-looking `Pure.pure` around already-wrapped values.
  - Prefer stable helper names and local names in generated goals.
  - Keep readability changes behind elaboration and proof-regression tests.

- [x] **Consider renaming the Lean support namespace/package —
  DECIDED 2026-07-17: keep `CryptolToLean`, document provenance.**
  The name is exact parity with upstream Rocq's `CryptolToRocq`
  (`saw-core-rocq/rocq/handwritten/CryptolToRocq/`); a Lean-only
  rename would manufacture a backend divergence to fix a cosmetic
  issue, re-pin ~1,900 goldens/fixtures, and require a coordinated
  `saw-lean-example` update — right before the pre-release
  soundness audit needs clean baselines. Provenance note added to
  README.md (Layout). If it ever changes, it changes as a
  coordinated `CryptolTo{Rocq,Lean}` rename upstream. Full
  analysis: `doc/2026-07-17_swe-quality-review.md`.

- [ ] **Execute the 2026-07-17 SWE-quality review findings**
  (`doc/2026-07-17_swe-quality-review.md`; ranked there). Open items:
  - **(#1, merge gate — MOVED 2026-07-17)** Trust kernel relocated
    via `git mv` to `saw-core-lean/replay/lean-check-core.sh`;
    `Builtins.hs` path updated. Remaining release-packaging half:
    resolve via Cabal `data-files` instead of `SAW_LEAN_ROOT` — that
    work must ship the whole Lean lake project as data too, so it
    stays bundled with relocatable-install packaging.
  - **(#2, merge gate)** Split `Term.hs` (6,776 lines) along its
    existing banner sections — extract at least
    `SAWCoreLean/Obligations.hs` and `SAWCoreLean/Convention.hs`.
    Pure module reorganization; do BEFORE the pre-release soundness
    audit so the audit reviews final structure.
  - **(#3 residual — DONE 2026-07-17)** `support/lean-shape-test.sh`
    renamed to `lean-negative-test.sh`; header (which still said
    an interim name) and stale `shape/` mentions in `test.sh`/`ci.yml`
    updated.
  - **(#4)** Split TODO.md: open items stay; Audit History +
    Decision Log to durable `doc/` files; large COMPLETE blocks to
    `doc/archive/`.
  - **(#5)** Sweep superseded dated notes from `doc/` top level into
    `doc/archive/`, keeping durable docs + README-canonized dated
    refs.
  - **(#6 — DONE 2026-07-17)** `support-proofs/` renamed
    `support-lemmas/` (NOT the reviewer's `conformance/`, which
    collides with the `test.sh` verb of that name that deliberately
    excludes this category).
  - Nits: haddock note that `leanReplayGoalHash`/`ProofHash` are
    provenance labels, not integrity hashes. (`saw.cabal` doc
    pointer already fixed 2026-07-17.)

## Priority 3: Regression Coverage

- [ ] Build a comprehensive differential conformance suite.
  - Current planning note:
    `doc/2026-06-29_differential-conformance-plan.md`. This is the
    authoritative roadmap for treating conformance as complete SAWCore
    coverage: cover the actual SAWCore constructors (`App`, `Lambda`, `Pi`,
    `Constant`, `Variable`, `Recursor`, `Sort`, `ArrayValue`, `StringLit`),
    module/parser constructs, every Prelude/Cryptol-SAWCore family, and every
    known gap. Current Lean `noncomputable` markings or backend rejections are
    test targets, not scope exclusions.
  - Use `make test-saw-core-lean-conformance` from the `deps/saw-script`
    repository root for the focused backend conformance sweep. From
    `otherTests/saw-core-lean`, the local-development equivalent is
    `make conformance`. It intentionally runs only true conformance categories:
    - `differential/*`: positive executable litmus tests where SAW observes an
      outcome, Lean observes an outcome from the SAW-Lean emitted artifact, and
      the harness mechanically compares those observations.
    - `differential/*/.known-gap`: the real differential run fails at a pinned
      SAW producer, emitted-Lean, or Lean observer diagnostic. This records
      missing parity or an observation-path blocker; it is not a passing
      conformance case.
    - `saw-boundary/*`: expected rejection or obligation-boundary litmus tests.
    Broad examples, whole-module extraction examples, crypto/stress drivers,
    proof-discharge demos, emitted-shape goldens, and Lean support-library-only
    proofs do not belong in this gate.
  - WARNING: `drivers/conformance_*` and `support-proofs/conformance_*` are legacy
    litmus candidates/regression checks, not true differential conformance.
    Most of them do "SAW proves" + "Lean elaborates" + "separate Lean theorem";
    that is useful, but it is not a compared SAW-vs-Lean observation. Migrate
    useful cases into `differential/*` one feature family at a time.
  - Every concrete support-library realization that stands in for a SAWCore
    primitive should ultimately have true differential coverage: a SAW-side
    observed result and a Lean-side observed result from the emitted artifact.
  - Prefer small, named, cheap cases over large examples: bitvectors, Nat/Int,
    rationals, IntMod, vector helpers, records/tuples, error propagation,
    raw/wrapped adaptation, and fix/precondition obligation emission.
  - Classify each case explicitly as:
    - true SAW-vs-Lean differential conformance,
    - expected obligation/rejection for partial or undefined behavior, or
    - non-conformance regression/support/integration coverage.
  - Do not count a Lean-only proof, golden diff, or elaboration-only check as
    semantic conformance.
  - Status (2026-07-03): the true-differential suite is broad — 104
    `differential/*` rows spanning Boolean/scalar/bitvector/vector/tuple/record/
    string primitives, algebraic/control recursors, parser/module constructs,
    and most Cryptol.sawcore dictionary and `ec*` entry points, all comparing a
    SAW observation against an observation of the emitted Lean. ~39 rows are
    pinned `.known-gap`s (stream helpers, direct recursors, floats, SMT arrays,
    residual runtime-`error` crypto primitives, derived-index bounds). The live
    coverage matrix, not this list, is authoritative: `otherTests/saw-core-lean/CONFORMANCE.md`.
  - Remaining conformance work: (1) deepen observers — most rows collapse to a
    single Bool that is essentially always `true`, so a mistranslation that
    still reduces to `Except.ok true` escapes; observe full result values /
    multiple distinct outcomes / error outcomes (this is the fidelity-oracle
    upgrade referenced by the position-directed plan's Slice-fence reviews);
    (2) promote known-gap families as their backend surfaces land; (3) migrate
    any remaining useful `drivers/conformance_*` litmus candidates into
    `differential/*`.

- [x] Add obligation-shape tests for proof-carrying boundaries.
  - Current planning note:
    `doc/archive/2026-06-30_obligation-shape-testing-plan.md`.
  - These tests should inspect the actual emitted Lean artifact and check that
    soundness-sensitive surfaces expose the right contract while avoiding
    hidden totalization, obsolete helpers, unchecked axioms, or Haskell-side
    semantic shortcuts.
  - Planning rule: this phase is testing-only, like the differential
    conformance plan. Do not change backend semantics or Lean support-library
    semantics to make these pass. Missing obligation support must appear as a
    small corpus fixture, usually `.known-gap`, with a pinned failure
    diagnostic. Positive obligation fixtures must fail when the emitted
    contract is absent or bypassed; known-gap fixtures must fail when the pinned
    failure disappears so the case can be promoted.
  - First targets: partial-operation preconditions, fully applied
    `unsafeAssert`, generic `fix`, raw-position `Prelude.error`, and
    `MkStream`/stream totality.
  - 2026-06-30 checkpoint: added the dedicated `obligations/*` harness and
    expanded the corpus beyond the initial P0 rows. Positive obligation-shape
    fixtures now cover wrapped and raw-function `fix`, definitional and open
    fully-applied `unsafeAssert`, raw `Prelude.error` in Nat/function/proof
    positions, and `MkStream` totality. Known-gap obligation fixtures now pin
    direct partial-operation preconditions, representative proof primitives,
    all with-proof vector primitives, and direct recursor families.
  - 2026-06-30 checkpoint: expanded the obligation corpus for stream helpers
    and Cryptol wrappers without changing backend semantics. Positive
    obligation-shape fixtures now cover `streamMap`, `streamShiftL`,
    `streamShiftR`, and `streamScanl` as stream-producing helper lowerings.
    Cryptol zero-divisor/zero-denominator wrappers (`ecDiv`, `ecMod`,
    `ecFieldDiv`, `ecRecip`, `ecSDiv`, `ecSMod`) also have positive
    obligation-shape coverage.
    `streamGet` finite projection is intentionally kept as value/differential
    coverage, not a fake standalone obligation test. Later updates promote the
    zero-divisor wrappers and finite `ecAt` to checked obligation rows.
  - 2026-06-30 checkpoint: promoted `ecSDiv` and `ecSMod` from known-gap
    rows to positive obligation-shape tests. Their emitted artifacts expose
    `ecSignedBVNonzeroM` and checked `ecSDiv_checkedM` / `ecSMod_checkedM`
    helpers, and assert absence of residual `Nat__rec` and unchecked direct
    signed-BV bypasses.
  - 2026-06-30 checkpoint: added obligation known-gap fixtures for P2 datatype
    and list surfaces: direct `List`/`ListSort`/`FunsTo`, direct user-defined
    SAWCore datatype recursors, and Cryptol algebraic enum lowering. These are
    not backend fixes; they pin the current rejection/realization gaps as
    corpus entries so they cannot remain prose-only.
  - 2026-06-30 checkpoint: expanded proof-primitive obligation known gaps to
    include `uip`, `bvEqToEq`, `foldr_nil`, and `head_gen`, and added loaded
    SAWCore primitive/axiom declaration fixtures plus an injected-Lean-code
    fixture. The injected-code fixture documents the current public API gap:
    term emission ignores module-level `injectCode`, and there is no public
    generic SAWCore-module Lean writer for the obligation corpus yet.
    Also added the remaining explicit positive rows from the obligation plan:
    non-definitional/provable `unsafeAssert` equality and raw index/proof
    `fix` alongside the existing raw function-position `fix`.
  - 2026-06-30 checkpoint: completed the obligation-shape testing plan as a
    testing corpus. The current conformance target reports all remaining
    missing proof-carrying surfaces as explicit known gaps; this is the
    guardrail for the next backend implementation phase, not proof that those
    surfaces are implemented.
  - 2026-06-29 checkpoint: expanded `saw-boundary` expected-rejection coverage
    for mapped-but-unsupported primitives. The new fixtures pin explicit
    diagnostics for unsupported Int primitives (`intAbs`, `intMin`, `intMax`),
    vector primitives (`head`, `tail`, `EmptyVec`, `scanl`), with-proof vector
    variants, SMT-array primitives, and under-applied `unsafeAssert`. These are
    not backend fixes; they make sure unsupported surfaces fail loudly until a
    proof-carrying implementation exists.
  - 2026-06-29 checkpoint: added proof-carrying surface coverage. A focused
    conformance driver pins fully-applied `unsafeAssert` as a visible Lean
    equality obligation consumed by `coerce`. A boundary fixture pins explicit
    rejection for representative SAW-internal proof primitives and lemma axioms
    (`uip`, `coerce__eq`, Nat/vector/bv lemmas, and size-bound assertions)
    until each has a Lean-checked realization.
  - 2026-06-29 correction: removed broad legacy/example buckets from
    `make conformance`. The conformance suite is a tight litmus boundary, not
    a place to jam large examples. Existing command-level parity drivers,
    Cryptol-source feature buckets, whole-module extraction examples, E-series
    proofs, LLVM examples, and crypto/stress examples remain available under
    the full `test` sweep or manual runs, but conformance work should extract
    focused `differential/*` or `saw-boundary/*` cases from them instead of
    promoting them wholesale.
  - Existing large examples that have exposed real gaps should be mined into
    focused litmus tests:
    - legacy `arithmetic` and `cryptol_chacha20_core_iterate` expose missing
      checked divisor/precondition obligations;
    - `cryptol_module_rational` exposes missing nonzero denominator obligations
      for rational literals;
    - `cryptol_module_error_string` exposes missing divisor obligations on a
      whole-module path.
    These gaps are already represented in `conformance_zero_divisor_obligations`
    or should be split into smaller conformance drivers before entering the
    gate.
  - Remaining conformance backlog from the mapped support surface:
    - Injected-code declarations: no public generic SAWCore-module Lean writer
      path currently exposes `InjectCodeDecl` to the conformance harness. Add a
      small scoped fixture as soon as injected declarations can reach the Lean
      module emitter without using hand-written Lean.
    - Direct `Void`: `Void` has no closed value source. Keep `EmptyType` and
      eliminator coverage, and add a direct `Void` boundary only if a genuine
      source term can reach the backend.
    - Checked Lean proof-library coverage for nontrivial Rational arithmetic.
      The SAW driver proves the source facts and the emitted Lean elaborates,
      but the local Lean environment has no lightweight checked Rat arithmetic
      tactic; do not use `native_decide`, because that introduces proof-local
      native-evaluation axioms.
    - `leNat` differential coverage once the SAW-side closed-term panic is
      avoided or a different clean SAW proof path is available.
    - `Float`, `Double`, `mkFloat`, and `mkDouble`: SAW currently exposes no
      equality or eliminator surface that makes these bindings observable in a
      clean differential test. A direct probe showed the Lean backend emits
      these primitive terms rather than rejecting them, but elaboration-only
      checks do not count as conformance. Keep documented until there is an
      observable source-level property to compare.

- [ ] Pin audit findings with focused regression tests as code is removed.
  - Assert obsolete direct fix helpers do not appear in generated output unless
    the output also contains the checked proof-carrying contract that justifies
    the helper.
  - Add negative/diagnostic coverage for generic primitive or axiom emission
    once those paths become reject-by-default.
  - Maintain small closed-numeral and imported-name tests around macro or
    realization behavior, so replacements preserve the user-visible cases
    without trusting Haskell-side equivalence.
  - 2026-06-29 audit priority: keep expanding the conformance suite.
    `bvLg2` is now pinned; zero-divisor paths must be tested as explicit
    obligation/rejection surfaces rather than as total operations.

- [x] Build and maintain an explicit Rocq parity matrix.
  - Map every `otherTests/saw-core-rocq/*.saw` driver to a Lean analogue or a
    documented, principled rejection.
  - Include `write_lean_cryptol_module` drivers in the required parity set.
  - Track whether each driver only emits text, elaborates under Lean, or has a
    corresponding human/automation proof.
  - Do not count a test as parity if it elaborates only by erasing an error,
    widening an axiom, or relying on unchecked Haskell-side reasoning.
  - Current reference: `doc/archive/2026-06-26_rocq-parity-matrix.md`.
  - Full SHA512 is not required to close this matrix. Treat it as a future
    scalability/stress test unless a smaller focused term exposes a general
    parity bug.

- [x] Close command-level Rocq parity gaps.
  - Added `write_lean_cryptol_primitives_for_sawcore`, mirroring Rocq's
    regeneration command.
  - Added focused driver coverage that emits and elaborates the generated
    Cryptol primitives module.
  - Keep `write_lean_cryptol_module` in the required validation set.

- [ ] Close small direct-driver Rocq parity gaps.
  - Added arithmetic divide-by-zero case; focused driver test elaborates and
    passes with refreshed goldens.
  - Added missing boolean `t2`/`t10` and offline reverse/implication cases;
    focused driver tests elaborate and pass with refreshed goldens.
  - Added missing sequence update-first/update-last/update-multiple,
    comprehension, and transpose cases;
    focused driver test elaborates and passes with refreshed goldens.
  - Added direct record update, tuple update, relative update, and nested-field
    update cases; focused driver test elaborates and passes with refreshed
    goldens.
  - Added octal literal coverage. (Polynomial-literal disposition since
    revised 2026-07-14: constant-error lowering, no obligation — see the
    raw-error disposition doc.)

- [ ] Add focused shape tests.
  - Datatype-parameter recursor fields where the actual parameter is
    function-shaped.
  - Partial applications through `ite`, wrapped helpers, and higher-order
    arguments.
  - `Nat` as raw index versus wrapped value result, especially `bvToNat` and
    related conversions.
  - Shared `let` RHS dependencies where later RHSs reuse earlier wrapped
    bindings.

- [ ] Add soundness boundary tests.
  - Generic `Prelude.fix` obligation emission.
  - `fix_unfold` rejection.
  - Residual per-index error rejection.
  - Raw/proof/type-position error rejection.
  - Unsupported higher-order rawification rejection.

- [ ] Keep broad validation gates green.
  - `git diff --check`
  - `cabal build exe:saw`
  - `cabal test saw-core-lean-smoketest`
  - Driver and boundary sweep under `otherTests/saw-core-lean`
  - Lean support library build
  - Focused proof examples once Phase-beta proof ergonomics are updated
  - 2026-06-29 checkpoint: fixed `otherTests/saw-core-lean/Makefile` to export
    an absolute `SAW` path; the orchestrator `cd`s into test subdirectories, so
    a relative binary path made local full-suite runs fail before exercising the
    backend.

- [x] Harden only the proof-harness checks needed to trust prototype
  regressions.
  - This is not the full SAW-side proof-check feature. It is the minimum
    discipline needed so tests cannot accidentally validate bad emission.
  - Require proof tests to expose a specific checked theorem of the expected
    goal type, rather than accepting any elaborating `proof.lean`.
  - Reject proofs whose checked theorem depends on `sorryAx`, including the
    generated `goal_holds := by sorry` stub. Use Lean's axiom reporting rather
    than text-only `sorry` scans.
  - Reject new unchecked proof-test axioms except for an explicit allowlist of
    support-library TCB axioms.
  - Ensure proof tests depend on freshly generated or tracked emitted artifacts;
    avoid ignored stale `.lean` files as the only source of truth.
  - Defer stronger provenance/skeleton matching for `completed.lean` unless
    tests start relying on completed outlines broadly enough that mutation risk
    can mask emission bugs.
  - 2026-06-27 checkpoint: `lean-proof-test.sh` now stages tracked
    `.lean.good` artifacts, requires `goal_closed : goal` for offline-goal
    outputs, and runs `#print axioms` on checked proof theorems. The allowlist is
    Lean's standard kernel axioms plus the two current support-library
    Vec/BitVec round-trip axioms.

## Priority 4: Proof Ergonomics

- [ ] Refresh the example/proof corpus as product workflow coverage.
  - Goal document:
    `doc/archive/2026-07-01_example-proof-backend-refresh-goal.md`.
  - Current inventory:
    `doc/archive/2026-07-01_example-refresh-inventory.md`.
  - This phase treats examples as instances of the intended SAW-Lean use case:
    SAW emits a Lean proof obligation, a user/assistant supplies a Lean proof,
    and Lean checks that proof against the current emitted artifact.
  - The task is classification plus principled repair, not "make all old
    examples green". Every example should become a current proof-backend
    example, current emission example, explicit proof gap, backend gap, final
    boundary, stress case, or retired legacy example.
  - If an example cannot be completed without backend design work, reduce or
    link it to a minimal conformance/obligation/boundary row and record the
    blocker here before moving on.
  - 2026-07-01 baseline after the E-series checkpoint: full
    `make -C otherTests/saw-core-lean test` reports 30 failures, all in
    driver/example emission surfaces, while the conformance, obligation,
    boundary, and default proof-harness categories behave as intended. The
    failures are mostly stale checked-obligation goldens, stream/recursor gaps,
    under-applied proof-carrying/indexing gaps, and large Cryptol/LLVM examples
    now exposing proof-carrying obligations.
  - 2026-07-01 inventory checkpoint: every current
    `drivers/*`, `proofs/*`, `proof-gaps/*`, and `stretch/*` row has an
    initial classification. The immediate small-example candidates are
    reviewed refreshes for `offline_lean`, `offline_lean_e_series`,
    `arithmetic`, and the small conformance-style driver goldens. Do not
    refresh or hide the real blockers: `conformance_stream`, `implRev4`,
    stream/fix module examples, and large crypto/LLVM rows remain
    backend-gap, proof-gap, or stress items until reduced or handled by a
    principled design.
  - 2026-07-02 support-proof bucket checkpoint: support-library-only rows
    such as `proofs/conformance_*` and `proofs/cookbook` were moved to
    `support-proofs/*`, which still runs in the default sweep but is not
    advertised as generated proof discharge.
  - 2026-07-01 E-series checkpoint: `E3_point_commutes` is back in the
    current-proof set after a principled recursor/binder shape fix pinned by
    `differential/record_projection_binder`. `E4_map_id` and
    `E5_littleendian` moved to `proof-gaps/` because current emission exposes
    the intended checked bounds obligations with local proof placeholders;
    treating the old pre-obligation proofs as green would be false. The
    `offline_lean_e_series` driver goldens were reviewed and refreshed only for
    this current proof-carrying emission shape.
  - 2026-07-01 `offline_lean` checkpoint: focused driver now passes after a
    reviewed `t6` refresh. The diff is the expected move from
    `genM`/`atWithDefaultM`/fallback indexing to `genWithBoundsM`,
    `atWithProof_checkedM`, and visible bounds obligations for the small
    reverse property. This is current emission coverage, not proof discharge;
    no Lean automation or Haskell-side bounds reasoning was added.
  - 2026-07-01 `arithmetic` checkpoint: focused driver now passes after
    reviewed refreshes for `t2`, `t3`, `t4`, `t11`, and `t12`. The refreshed
    goldens expose checked BV nonzero obligations for division/remainder and
    checked bounds obligations for bitvector extension indexing. This is
    current emission coverage, not proof discharge; do not add backend
    arithmetic reasoning or Lean automation to make these obligations vanish.
  - 2026-07-01 small conformance-style driver checkpoint:
    `conformance_bitvector`, `conformance_scalar`,
    `conformance_scalar_extra`, `conformance_string_bytes`, and
    `conformance_zero_divisor_obligations` now pass focused driver tests after
    reviewed checked-obligation golden refreshes. They remain legacy smoke
    examples; the real conformance gate is the differential/obligation suite.
  - 2026-07-03 vector driver checkpoint: `conformance_vector` and
    `conformance_vector_zip` now pass focused driver tests after reviewed
    golden refreshes. Their `atWithDefaultM` occurrences are source-level
    `atWithDefault` behavior, not fallback/defaulting for checked indexing.
    They are current-emission smoke rows; the real conformance gate remains the
    differential/obligation suite.
  - 2026-07-01 small whole-module/projection checkpoint:
    `cryptol_chained_projection_share`, `cryptol_module_enum`,
    `cryptol_module_error_string`, and `cryptol_module_rational` now pass
    focused driver tests after reviewed golden refreshes. These are current
    emission smoke rows only; enum/ListSort, source-level error,
    partial-operation, and rational proof/library conformance remain tracked by
    the focused differential/obligation rows.
  - 2026-07-01 prelude auto-emit checkpoint: `sawcore_prelude_auto_emit` now
    passes again after a general recursor motive-shape fix. Opaque local type
    families of type `... -> Sort u` stay raw rather than being mistaken for
    value-domain motives and wrapped with `Pure.pure`; the record-projection
    binder regression and E-series driver still pass.
  - 2026-07-01 full-harness checkpoint after reviewed refreshes: full
    `make -C otherTests/saw-core-lean test` now reports 18 driver failures.
    The remaining failures are classified blockers, not safe unreviewed
    golden drift: stream/recursor wrapping, direct vector `atWithDefaultM`
    fallback migration, wrapped dictionary/record-rec gaps, under-applied
    proof-carrying `at`, recurrence/bounds proof gaps, and large crypto/LLVM
    stress rows.
  - 2026-07-01 wrapped dictionary/record-rec reduction checkpoint: added
    `differential/cryptol_vector_eq_dictionary` as a minimal known-gap row for
    the failure exposed by `cryptol_module_simple` and
    `cryptol_polymorphic_class_dict`. SAW executes the function-valued
    `PEqSeq` example, Lean imports the emitted artifact, and the harness pinned
    the diagnostic where an Eq dictionary was available as
    `Except String (RecordType ...)` but `RecordType.rec` expected the raw
    record.
  - 2026-07-02 raw/wrapped recursor checkpoint: promoted
    `differential/cryptol_vector_eq_dictionary` and the focused Unit/function
    recursor obligation rows. The backend now binds wrapped scrutinees only in
    value-producing contexts, including value-producing function recursors via
    eta expansion or full post-scrutinee application. This was fixed without
    rawifying dictionaries or recognizing `PEqSeq`/`RecordType.rec` by name.
    2026-07-03 update: the `drivers/sequences.t18` higher-order wrapped
    function application mismatch around `foldl (+)` is closed by the
    fold-family value-function convention and pinned by `differential/vector_fold`.
    Keep any remaining `sequences` drift out of the recursor/dictionary bucket.
  - 2026-07-02 record-update proof checkpoint:
    `drivers/cryptol_module_record_update`,
    `drivers/cryptol_module_point`, and `proofs/point_shift_property` all pass
    focused tests against current emitted artifacts. `point_shift_property`
    remains a real proof-backend example, not a proof gap.
  - 2026-07-02 proof-gap note checkpoint: added explicit gap notes for
    `proof-gaps/cryptol_running_sum_verify` and
    `proof-gaps/offline_lean_popcount32` so recurrence/popcount examples are
    visible as proof-support blockers rather than unexplained stale failures.
  - 2026-07-02 gap-inventory checkpoint: every `proof-gaps/*` directory now has
    a local `GAP.md` note and `source.txt`, and `make -C
    otherTests/saw-core-lean gaps` / `make test-saw-core-lean-gaps` reports
    proof/stress gaps as tracked inventory rather than silent skips. The
    default sweep also inventories these rows separately from passing
    proof-discharge examples.
  - 2026-07-03 proof-audit checkpoint: all default `proofs/*` examples pass
    under `lean-proof-test.sh`. The explicit proof-gap attempts remain gaps:
    E4/E5 fail because emitted artifacts still contain unresolved checked
    bounds obligations, large crypto/LLVM proofs remain proof-support or
    scalability problems, and `cryptol_chacha20_core_iterate` should not be
    promoted until its current large artifact is refreshed/reviewed and the
    Nat div/mod checked-helper drift is reduced or otherwise tracked.
  - 2026-07-12 E4/E5 promotion checkpoint: `proof-gaps/E4_map_id` and
    `proof-gaps/E5_littleendian` are closed and promoted to `proofs/` via the
    completed-outline workflow. Each row stages a `completed.lean` whose
    embedded `h_bounds_` evidence is discharged with checked tactics
    (`assumption` for direct `genWithBoundsM` binder bounds; for E5's derived
    `subNat 3 i` indices, `simp only` macro/`subNat`/`Nat.sub_eq`
    normalization plus `omega`); the harness def-eq-checks the completed goal
    against the generated goal, and both outer proofs pass the axiom audit
    with no new automation and no support-library changes. Two findings for
    later work: (a) the emitted evidence tactic
    `(first | assumption | skip); all_goals sorry` cannot close derived-index
    bounds, so raw artifacts with derived indices carry `sorryAx` inside the
    goal statement until a user completes the outline — consider teaching the
    emitted chain the same checked normalization+`omega` step; (b) `omega`
    does not recognize bare `Nat.sub` applications (from reducible `subNat`),
    so `Nat.sub_eq` is the required bridge rewrite.

- [ ] Refresh generated goldens and proof examples after proof-carrying
  emission changes.
  - The default `otherTests/saw-core-lean` sweep no longer treats full SHA512 as
    required, but many checked-in `.lean.good` files still reflect the earlier
    generated naming/proof-obligation shape.
  - Several proof harness examples still target raw-era or pre-obligation terms
    and now fail because generated goals contain wrapped binds or unresolved
    productivity/fixed-point obligations.
  - This is proof ergonomics/regression-maintenance work, not a reason to
    weaken the proof-carrying soundness interface.
  - 2026-06-27 checkpoint: the small non-recursive proof examples now validate
    the current wrapped emission style (`E1`, `E2`, `E3`, `E7`, `offline_t1`,
    `offline_t3`, `offline_t4`, `tuple_fst`, `point_shift_property`,
    `cookbook`, and `walkthrough`). Remaining failures are informative:
    monadic vector helper goals need checked `genM`/`atWithDefaultM`/`foldrM`
    proof lemmas; large crypto goals still time out under direct unfolding; and
    recursive examples cannot be discharged externally while emitted files
    contain local productivity witnesses as `by sorry`.
  - 2026-06-28 checkpoint: driver goldens and the driver harness now reject the
    deleted direct fix-helper surface. The harness was tightened to elaborate
    and scan all emitted `.lean` files in a driver directory, including names
    that do not begin with the `.saw` basename.

- [ ] Keep recursive/fix emission on the generic proof-carrying path.
  - Direct fix-shape helper surfaces (`mkStreamFix*`, `genFix*`,
    `GenFix*`, `StreamBodyProductive`, `PairStream*`,
    `saw_unreachable_default`, and `saw_productivity`) have been deleted from
    the Lean support library. They represented a false-start architecture where
    Haskell selected semantic lowerings and Lean merely checked side conditions.
  - Current rule: Haskell emits the literal SAWCore fixed-point body and the
    Lean propositions required to justify using it. Any ergonomic rewrite from
    the literal obligation to a cleaner recurrence must be a Lean theorem or
    proof-script hint, not a trusted Haskell classifier.
  - Obsolete proof examples built around the deleted helpers were removed
    (`E6_popcount`, `cryptol_running_sum_eq`, `popcount32_via_bridge`,
    `recursion_stream_corec`, `stream_fibs_corec`, and the
    `shape/productivity_contract` probes). Replacement examples should be
    rebuilt against the generic obligation surface once that emitted shape is
    stable.
  - Remaining work: harden completed-outline validation so proof examples
    cannot drift from the generated obligation, then add small recurrence
    examples that prove explicit generic fix contracts without reintroducing
    special-purpose helper APIs.

- [ ] Add Lean simp support for Phase-beta generated goals.
  - Normalize common `Except.ok` / `Pure.pure` / `Bind.bind` patterns.
  - Add lemmas for generated helpers such as `iteM`, `genM`,
    `atWithDefaultM`, `vecSequenceM`, stream/fix helpers, and bitvector
    operations.
  - Avoid lemmas that erase `Except.error` or hide unsupported cases.
  - Prefer `grind` and targeted simp lemmas as checked proof automation. Do not
    solve proof-library gaps by adding accepted `bv_decide`/`bv_check` proofs;
    BV-heavy cases can stay as explicit obligations until there is an
    axiom-clean proof route.
  - 2026-06-27 checkpoint: replaced the width-4 `vecSequenceM` probe with the
    general theorem `vecSequenceM_ok_of_get`, which states the principled eager
    sequencing contract: if every wrapped vector element is `Except.ok`, the
    whole `vecSequenceM` is `Except.ok` of the pure vector. Literal-vector
    conveniences should be corollaries of this all-width theorem, not new
    width-specific proof rules.
  - 2026-06-27 checkpoint: added `atWithDefaultM_vecSequenceM_ok_lt`/`_ge`
    and `foldrM_pure_eq_foldr`. These extend the same pattern to selected
    indexing through eager sequencing and to right folds: the proof script must
    provide all-elements or all-steps success evidence before Lean rewrites to
    the pure helper.

- [ ] Update proof examples for wrapped generated goals.
  - Cookbook examples should show the current generated theorem shape, not the
    old raw-era shape.
  - Add small stable proof scripts that users can copy.
  - Keep proof scripts narrow enough that regressions identify a real backend
    or ergonomics issue.
  - Quarantine or mark BV-heavy crypto examples that currently need
    `bv_decide`; they are useful stress cases, but they should not be counted as
    green proof regressions under the current trust policy.
  - 2026-06-27 checkpoint: `support-proofs/cookbook` now pins small wrapped-helper
    examples for `vecSequenceM`/`atWithDefaultM` and `foldrM`, giving users a
    copyable proof shape that preserves eager `Except` semantics.

- [ ] Decide the external proof-obligation format.
  - Current productivity obligations are split local lets in emitted Lean.
  - The current checked path is edit-in-place generated proof files:
    proof tests may provide `completed.lean`, which is treated as the
    user-completed generated outline and must elaborate without any `sorry`.
  - Later ergonomics work can decide whether to lift local obligations into
    top-level declarations with explicit dependency binders.
  - 2026-06-28 checkpoint: `completed.lean` is now checked against the tracked
    generated `.lean.good` artifact. The harness imports the generated artifact
    under a private namespace and requires `GeneratedHarness.goal = goal` by
    `rfl`, so completed outlines may simplify only by Lean definitional
    equality. Any non-definitional rewrite must be exposed as a separate
    Lean-checked proof artifact, not hidden in the edited outline.
  - 2026-06-29 audit finding: this harness is strong enough for trusted
    regression fixtures, but not for product replay. The final checker should
    generate a separate file that refers to fully qualified fresh obligation
    names, rather than appending unqualified checks inside the user's proof-file
    namespace.

## Priority 5: SAW-Side Proof Checking

- [x] **Add an integrated SAW-side proof-check command (DONE 2026-07-16).**
  Design + seven-audit record: `doc/2026-07-16_replay-design.md`.
  - Emit-only mode (`offline_lean`) produces obligations without claiming
    success (`SolveUnknown` since 2026-07-14).
  - Check mode (`offline_lean_replay`) takes a completed Lean proof file,
    re-emits the obligation fresh in-process (fresh emission is the authority;
    the goal-telescope arity pin in `writeLeanProp` refuses emission on
    quantifier drift), stages user proof + `completed.lean` against it, and
    runs the factored `saw-core-lean/replay/lean-check-core.sh`
    trust kernel: cleared `LEAN_PATH`, non-degradable timeout, placeholder
    policy, anti-trivialization probe, completed-outline drift check,
    user-file sorry scan, closer-type probe, and an EXACT-match axiom
    allowlist (the four full axiom names — no suffix matching). Only on full
    success does SAW record `LeanReplayEvidence` (toolchain, goal hash, proof
    hash, axioms; surfaces as `Theorem (Lean kernel replay)` /
    `verified-lean-replay` in verification summaries).
  - Pinned by `workflows/replay_e1_verify`, `workflows/replay_running_sum_verify`
    (positive) and `saw-boundary/replay_reject_{sorry,axiom,suffix_axiom}`
    (negative). Full conformance pass 2026-07-17.
  - Recorded follow-ups (not blockers): rebase the CI proofs harness onto the
    same factored checker so the single-checker principle holds by mechanism;
    strengthen the telescope pin from arity to binder-type comparison (a
    same-arity wrong-type binder currently passes the pin, though the proof
    would then fail to elaborate).
  - Audit triage (RESOLVED 2026-07-14): `offline_lean` formerly behaved like
    Rocq's offline exporter and marked the SAW goal solved after writing the
    file. It is now EMIT-ONLY, and replay is the sole discharge path.
  - 2026-06-28 audit finding: driver tests that pin `Proof succeeded!` plus
    generated `by sorry` are emission/elaboration tests only. They must not be
    counted as checked proof-discharge regressions.

## Audit History

Moved to `doc/audit-history.md` (2026-07-17 doc reorganization).

## Decision Log

Moved to `doc/decision-log.md` (2026-07-17 doc reorganization).

## References

- `doc/archive/2026-07-08_position-directed-translation-plan.md` (concluded
  2026-07-11; the operative plan is `doc/2026-07-14_release-plan.md`)
- `doc/archive/2026-07-03_direct-recursor-semantics-design.md`
- `doc/archive/2026-06-26_phase-beta-expected-shape.md`
- `doc/archive/2026-06-26_expected-shape-todo.md`
- `doc/archive/2026-07-01_complete-wrapping-migration-goal.md`
- `doc/2026-07-02_position-callee-calculus.md`
- `doc/archive/2026-07-02_position-callee-conventions-design.md`
- `doc/archive/2026-07-02_position-callee-conventions-goal.md`
- `doc/archive/2026-05-14_wrap-invariant-audit.md`
- `doc/2026-05-02_residual-trust.md`
- `doc/archive/2026-06-28_clever-legacy-path-audit.md`
- `doc/archive/2026-06-29_comprehensive-audit.md`
- `doc/proof-cookbook.md`
