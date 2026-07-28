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
