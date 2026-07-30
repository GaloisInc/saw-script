# Decision Log

Living record of ratified design decisions. Moved out of TODO.md
in the 2026-07-17 doc reorganization.

- [x] Treat Lean as a proof backend, not just an emitter.
- [x] Treat Rocq feature parity as the top-level feature goal; proof discharge
  is required but not exclusive.
- [x] Preserve SAWCore errors with `Except String`.
- [x] Reject unsupported primitives by default.
- [x] Remove the old emitted-Lean result-shape classifier.
- [x] Remove broadly defaulting stream helpers from the Lean support library.
- [x] Treat soundness-side conditions as emitted Lean obligations, not Haskell
  automation requirements.
- [x] Treat Haskell semantic classifiers as migration scaffolding, not the
  trusted long-term design. When a classifier justifies recursion,
  productivity, totality, or rawification, prefer moving that justification into
  Lean as a named theorem, checked helper, or tactic-proved obligation.
- [x] Permit classifiers as untrusted proof emitters: they may recognize a
  generated shape and emit helpful Lean lemmas/scripts, provided the backend
  still emits the regular contract and trusts only the kernel-checked evidence.
- [x] Treat arbitrary SAWCore `Prelude.fix` as in scope for emit-stage
  proof-carrying translation via an explicit unique-fixed-point obligation.
  This does not mean arbitrary fix is automatically discharged.
- [x] Prioritize emission correctness and stable generated Lean before adding
  integrated SAW-side proof-check UX.
- [x] Split auto-emitted Prelude declarations into raw logical definitions and
  wrapped value-domain facades.
- [x] Reject `bv_decide`/`bv_check` as accepted proof-discharge mechanisms under
  the current no-extra-trust policy, because substantial uses introduce
  proof-local native-evaluation axioms. Use checked Lean proof automation
  (`grind`, `simp`, `omega`/`bv_omega`, `cbv`, helper lemmas) where it works,
  and leave hard BV obligations open rather than widening the trusted base.
- [x] Decide and start encoding the position/callee convention design before
  further local wrapping fixes. The 2026-07-03 raw-logical slice introduced the
  explicit convention vocabulary and routed `Eq`/`Refl`/`Eq.rec` through it.
  Remaining convention surfaces should extend this design by new declared
  positions/callee contracts, not by local patches.

- [x] AMEND the bv_decide rejection into a TWO-TIER trust policy
  (2026-07-21, user decision: "show we can discharge with bv_decide but
  note this clearly as something that should be resolved later"). The
  strict tier is unchanged and remains the default. A per-row,
  loudly-labeled `native-eval` tier (row-local `.trust-tier` file)
  admits bv_decide's per-invocation proof-local native axioms — and
  nothing else — for genuinely SAT-shaped fixed-width goals
  (quarterround/SWAR class). Tier names and admissions live solely in
  `replay/axiom-audit.awk`; stale markers, unknown tiers, and forged
  axiom declarations all fail loudly (mutation-tested by
  `support/trust-tier-selftest.sh`). Recorded resolution: migrate tier
  rows to the strict tier by swapping `bv_decide` -> `smt` when
  lean-smt's cvc5 BV proof reconstruction becomes usable upstream.

- [x] DISPOSITION LIB-1 as ship-documented (2026-07-28, user
  decision: "this can just be a clearly-flagged note in the
  backend-specific README with a known remedy for later releases").
  Context: the differential row landed (`lazy_vector_error_slot`),
  scope was measured (59/350 artifacts, 57 via the evidence-less
  checked-indexing route — `doc/2026-07-28_lib1-scope-measurement.md`),
  and the (b-evidence) interim gate was scrutinized and REFUTED
  (`doc/2026-07-28_lib1-b-evidence-design.md`). Severity assessment
  informing the decision: adversarially constructible and reachable
  from ordinary Cryptol, amplified by compositional chains — but a
  narrow false-statement class, zero landed proofs affected
  (discharges close at explicit Except.ok), and undetectable by any
  proof-side gate in principle. Disposition: README "KNOWN SOUNDNESS
  LIMITATION" flag carrying the second-party "LeanReplayEvidence
  modulo LIB-1" caveat + residual-trust §3.2e (the catalog's one
  live-defect entry); NO interim rejection gate. Recorded remedy:
  the (a) faithful per-element carrier, scheduled with 0.03; entry
  closes when the pin row flips to true coverage.

- [x] SEQUENCE the Family-3 emission pass BEFORE the pre-release
  audit (2026-07-28, user decision, in answer to "are these
  symptoms of a wider problem? do we need an audit or a plan?").
  Analysis: `doc/2026-07-28_defect-families-and-sequencing.md` —
  every finding from both audits sorts into three families; two
  (trust-kernel-asks-text-questions, no-model-of-partiality) have
  named roots and written plans and are deferred past the audit BY
  DECISION; the third (emission conventions: F-8/F-1/A-4/F-6/F-7/
  F-2 core) had neither, which is why its fixes read as
  whack-a-mole. Proposed root recorded: the calculus made
  ADAPTATION safe via the adaptTo chokepoint but left ANNOTATION
  unguarded — a definition's declared type is computed by a
  different path from its body, over a binding vocabulary too
  coarse to carry the invariant. Decision: write the plan (state
  the invariant, give it a chokepoint), execute it as ONE pass with
  the Term.hs split and the three open emission items as instances,
  and only then run the panel — an audit is for finding what we do
  not know, and auditing first would spend lanes rediscovering
  F-1-class issues in code about to be restructured. The audit is
  NOT skipped: the deferred families' dispositions and the
  possibility of a fourth family are precisely its job.

- [x] QUALIFY the emitted recursor head (F-2 core), 2026-07-29, in
  the Family-3 pass. This is a NAMING-CONVENTION decision, not a
  refactor: it changes what a user writes in a discharge, from
  `@Num.rec` to `@CryptolToLean.SAWCorePrimitives.Num.rec`.
  Context: the head was emitted SHORT while its ctor-order assertion
  was emitted QUALIFIED, so `@Stream.rec` was genuinely ambiguous
  against Lean core's root-scope `Stream` and resolved by
  overload-by-elaboration — and had it ever resolved to the core
  inductive, the assertion would still have passed while checking a
  different one. Deferred 2026-07-25 with the blast radius measured
  (15 emitted rows; five hand-written artifacts plus two demo
  copies), explicitly to be taken "with the naming pass, not alone".
  Alternative considered and rejected: qualify only when the short
  name collides with something Lean's root scope provides. That is
  DETECTION — it needs a model of the root scope, which is the shape
  of machinery F-8 built and then deleted. Uniform qualification is
  by-construction, at the cost of verbosity in user discharges.
  Failure mode was LOUD either way (the scrutinee type pins the
  inductive), so this buys argument, not a fixed unsoundness.

- [x] RETIRE `negative/underapplied_partial_illtyped` (2026-07-29),
  on landing F-1's fix. The probe pinned that the under-applied
  partial-op emission stays ILL-TYPED, so that its failure mode is
  loud rather than silently absorbed. The fix makes the emission
  well-typed, so the probe's subject no longer exists — it is not a
  probe that started passing for the wrong reason (the V-H1 class),
  it is a probe whose question was answered. Its own text named this
  outcome in advance: "the honest fixes are a wrapped-convention
  signature or deleting the lowering". Replacement coverage is
  POSITIVE and stronger: `drivers/under_applied_partial_wrapper`
  elaborates three under-application shapes, so a regression to the
  raw annotation fails at Lean rather than in a golden diff.

- [x] FIX the trust kernel's threat model as ERROR, NOT ADVERSARIAL
  ACTION (D1, 2026-07-30, user decision during the down-scope
  discussion after wave 3). The model was previously unstated, and
  its absence is why three audit waves scored text-inspection
  defects (exploitable only by an author deliberately defeating the
  checker) as release-blocking CRITICALs alongside genuine
  emission-side soundness holes. Citable statement, in/out-of-model
  boundary, and the wave-3 findings re-scored under it:
  `2026-05-02_residual-trust.md` §Threat model. User-facing
  consequence in README ("What the replay checks defend against");
  reviewer-facing scope rule in contributing.md (before C1–C4).

- [x] NARROW the proof-source lint to its one closed job (D2 =
  plan 3a, 2026-07-30, user decision): keep only the check the
  error model needs — no top-level `axiom` declaration — and drop
  the open-ended command-head denylist that K-1 showed cannot be
  kept complete. Plan 3b (retiring the `native-eval` conformance
  tier, which owns the lint's only other load-bearing rule) is held
  IN RESERVE if the narrowed lint still cannot reach defect-free.
  Basis measurement: `2026-07-30_proof-lint-head-measurement.md`.

- [x] KEEP the completed-outline drift check, HARDENED (D3,
  2026-07-30, user decision): drift between a completed outline and
  the fresh emission is squarely in the error model, so the check
  stays — upgraded from a `#check`-grade probe to a kernel-checked
  declaration (`theorem __drift_binding : GeneratedHarness.goal =
  goal := rfl`), per contributing.md rule 5 ("ask Lean, not the
  text"; `#check` adds no declaration and is never kernel-checked).

- [x] DISCARD the out-of-model wave-3 fixes; down-scope K-2 (D4,
  2026-07-30, user decision — "we pivot here and where fixes are
  obviated, we throw them out"). K-1's allowlist inversion and
  CP-1's re-verification loop are dropped: both defend only against
  an adversarial author, and three rounds of fix-audits found
  defects in the fixes themselves faster than the fixes retired
  risk. K-2 is cut down to its in-model residue, the ~3-line C3
  fail-closed fix: `verify_unchanged` must FAIL when a staged file
  has vanished. Path-latching is dropped with the rest.
