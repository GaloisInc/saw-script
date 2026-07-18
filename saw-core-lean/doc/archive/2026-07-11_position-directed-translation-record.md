# Position-Directed Translation — execution record (COMPLETE 2026-07-11)

Extracted verbatim from TODO.md in the 2026-07-17 doc reorganization;
this was the operative-priority section while the refactor ran.
The plan doc is `2026-07-08_position-directed-translation-plan.md` (same dir).

## Operative Priority (COMPLETE 2026-07-11): Position-Directed Translation

Full execution plan: `doc/archive/2026-07-08_position-directed-translation-plan.md`.

This was the top technical focus through 2026-07-11; all eight slices
are complete and the records below are historical. The goal is to make the position/callee
calculus (`doc/2026-07-02_position-callee-calculus.md`) the *implementation* of
the term translator rather than a document it approximates. Today the translator
is bottom-up (translate naturally, repair shape with syntactic predicates such
as `shouldWrapBinder`, `isVariableHead`, `natValueResult`, `typeArgPositions`,
and — worst — `bindingShapeOfTerm`, which inspects the emitted Lean AST). The
calculus is top-down: expected position `ρ` is pushed from context and a term's
representation is a function of `(ρ, source term)`.

Why this is the deep priority: emission correctness is currently defended by
"Lean's typechecker rejects a wrong shape". That is sound for shape mistakes but
*not* for the surfaces where both representations typecheck — equality subject
representation, `Eq.rec` proof transport, and recursor constructor order — which
are silent-unsoundness risks the bottom-up heuristics cannot reason about.

SAW-side proof replay is deliberately NOT part of this work (at the time,
`offline_lean` still marked goals solved without invoking Lean; since
2026-07-14 it is emit-only). It is bounded end-game plumbing —
the test harness already implements the required checks (exact goal type,
`#print axioms` minus `sorryAx`, axiom allowlist) — and is tracked in
Priority 5.

Slices (each emitted-Lean-diff-reviewed and green before commit; see the plan
doc for per-slice regression fences and bounded validation commands):

- [x] **Slice 0** — instrument a `translateAt ρ t` seam + position trace,
  behavior-inert (migration safety net / oracle). `translateAt` +
  `shapeConsistentWithPosition` + `SAW_LEAN_TRACE_POSITIONS` trace in Term.hs;
  checked-application/proof-primitive wrapped args are the first declared-ρ
  call sites; byte-diff oracle: `support/emitted-lean-snapshot.sh`
  (`snapshot`/`diff` against `.snapshots/<name>`, "emitted" = untracked
  `*.lean`).
- [x] **Slice 1** — enrich `Γ` and `TranslatedTerm` to the full calculus record
  (source type, Lean ident, bound position, representation, exact Lean type);
  stop collapsing raw-value/index/proof/motive into one `BindingRaw`.
  `BindingInfo` record in `_bindingEnv`; `TranslatedTerm` carries
  `ttProducedAt :: Maybe ExpectedPosition` (bidirectional `TranslatedTerm`
  pattern = greppable not-yet-position-declared marker). Positions recorded
  only where unambiguous today (sort/wrapped/recursor-field/shadow/let-RHS);
  `skipBinderWrap`-conflated cases stay `Nothing` until Slice 3. Emitted Lean
  byte-identical to the Slice 0 baseline (snapshot oracle, 151 files).
- [x] **Slice 2** — make `adaptTo` the single adaptation chokepoint; delete
  `bindingShapeOfTerm`/`bindingShapeOfLeanTermM` (emitted-AST inspection).
  `adaptTo` implements exactly the allowed adapters; forbidden adaptations
  throw `ForbiddenAdaptation` (new `TranslationError`); the emitted-AST
  inspectors are deleted (variables read Γ, other shapes come from the source
  term form or the dispatch that computed them). Emitted Lean byte-identical
  to baseline — no current row exercises a forbidden path. Note:
  `bindingShapeOfType` (emitted-*type* classification at binder sites) remains;
  it is a Slice 3/4 demotion target.
- [x] **Pre-existing (not from this refactor):** `drivers/arithmetic` and
  `drivers/conformance_stream` goldens were stale since the position-callee-
  conventions work of 2026-07-03 (`55e4fe099`, `429452873`). Every diff hunk
  reviewed (only `@Eq.{1}` explicit universes and the stream `Pure.pure`-in-
  case-handler/`Except String Nat` motive change); goldens refreshed per-row
  2026-07-09, both rows green. Full 18-row `@Eq` sweep completed 2026-07-09:
  `@Eq.{k}` class and all elaborating bounds-overhaul rows refreshed;
  `llvm_chacha20_core_verify` kept red as the Slice 4 specimen (see below).
- [x] **Stream@core pair — DECIDED 2026-07-14 (release plan): migrate to
  expected rejection; DONE same day** (rows moved to
  `saw-boundary/cryptol_chacha20_{core_iterate,iround_zero}` with
  `.expect-fail` + rejection-diagnostic log goldens; success goldens
  retired to git history; GAP.md twins updated). Original record: `drivers/
  cryptol_chacha20_core_iterate` and `drivers/cryptol_chacha20_iround_zero`
  reject with `Refusing to translate primitive Prelude::Stream@core`
  (wrapped-scrutinee recursor convention); their goldens expect successful
  translation (verified failing at pre-refactor commit `89a6cef06`, so this
  predates the position-directed work). Decision: the rows become
  expected-rejection rows pinning the named diagnostic; the translation
  path (the `saw_self_ref_comp_iterate` parametric-bridge family / lazy
  selection) folds into the OP-3 successor design post-0.01. The old
  success goldens are retired with the reclassification, not refreshed. (`drivers/sawcore_prelude_auto_emit`, formerly also listed here,
  was RESOLVED 2026-07-10 by Slice 5c: the function-carrier equality
  convention plus the raw-mode raw-logical pipeline un-rejected the prelude;
  golden refreshed after per-hunk review — the only delta vs the
  pre-regression golden was the `Eq__rec` → `@Eq.rec` head — and the full
  emission elaborates with zero errors.)
- [x] **Pre-existing gaps found while probing the debts slice (2026-07-10,
  both LOUD; BOTH FIXED 2026-07-14 as release 0.01 workstream 5):**
  - FIXED — top-level `write_lean_term` of a runtime-computed Nat:
    `translateDefDoc` now annotates from the produced body's
    production record (a `BindingWrapped` body at a non-wrapping type
    wraps the annotation to the carrier it actually inhabits), never
    from a bare type translation alone. Pinned by
    `obligations/write_term_runtime_nat` (`def RuntimeNatProbe :
    Except String Nat`, elaborates).
  - FIXED — `PairValue` instantiated at a proposition: pair/tuple
    carrier family (`PairType`/`PairValue`/`PairType1`/`PairValue1`/
    `Pair_fst`/`Pair_snd`) rejects at translation with a named
    diagnostic when a type slot is a proposition (same `asEq`
    authority as the argument-mode domain analysis) instead of
    emitting `PairType (@Eq.{1} …)` that fails Lean elaboration
    downstream. Universe-generalizing the support inductive is 0.02
    candidate coverage work. Pinned by
    `saw-boundary/pair_prop_component_rejection`.
- [ ] **`saw_fix_unique_exists` is unsatisfiable for every strict wrapped fix
  body (found 2026-07-12 while pushing `proof-gaps/cryptol_running_sum_verify`;
  design gap, needs a contract revision doc before any code change).** The
  contract's uniqueness clause quantifies over all `z : Except String α`
  (`∀ z, body z = z → z = pure x`), but any emitted body that actually
  consumes its recursive argument — every real self-referential comprehension,
  e.g. `[0] # [ s + x | s <- sums | x <- xs ]` — propagates `Except.error`
  through the element binds, so `body (Except.error e) = Except.error e` for
  every `e`: errors are always fixed points and uniqueness is refutable.
  Kernel-checked counterexample (2-element analogue of the running-sum body):
  `¬ saw_fix_unique_exists (Vec 2 Nat) tinyBody` proves by exhibiting the
  error fixed point via `Vector.ofFnM_succ/zero` unfolding. Consequences:
  the recurrence-class examples (`cryptol_running_sum_verify`,
  `offline_lean_popcount32`, `cryptol_module_rec_ones`,
  `cryptol_module_stream_fibs`, the ChaCha20 iterate pair) emit obligations
  that elaborate but can never be discharged — sound (SAW never claims the
  goal) but unusable. The doc comment on the primitive ("an `Except.error`
  fixed point is not ignored") contemplated error fixed points as a safety
  feature without noticing they always exist for strict bodies.
  `saw_mkStream_total_exists` (pointwise totality) and the raw fix contract
  do not have this defect. Candidate revision: uniqueness among *pure* fixed
  points (`∃ x, body (pure x) = pure x ∧ ∀ y : α, body (pure y) = pure y →
  y = x`) plus an explicit soundness argument tying the unique pure fixed
  point to SAWCore's `fix` semantics; must go through a design doc and the
  soundness-contract review, not a quiet edit.
- [ ] **Eta-expanded checked-access wrappers embed bounds evidence that is
  unprovable at its position (found 2026-07-12 while refreshing
  saw-lean-example; same "sound but undischargeable" family as the fix
  contract above).** The prefix-partial checked-access convention emits
  `fun (η_checked_arg_0 : Nat) => let h_bounds_ : η_checked_arg_0 < n :=
  (by …); atWithProof_checkedM … η_checked_arg_0 h_bounds_` — the lambda
  claims a universal bound that is false for general `Nat`, so no
  completed-outline tactic can close it; only the emitted `sorry` inhabits
  it. In the demo's `implRev` goals the wrapper is consumed by an
  `Either.rec` over an Int sign-split (`xs @ ` computes the index via
  `natToInt`/`intSub`/`intToNat`), so the true bound is a non-local
  arithmetic fact. Consequence: `offline_lean` goals for `implRev`-shaped
  indexing (saw-lean-example invol/eq_spec) emit, elaborate (with
  `sorryAx` inside the goal statement), and can never be discharged
  sorry-free. Fix direction: the wrapper must RECEIVE evidence rather than
  fabricate it — either the dependent form `(i : Nat) → i < n → …` with
  call sites supplying the proof (they sit under `genWithBoundsM` binders
  or concrete indices that know the bound), or hoist the obligation to the
  goal boundary. Related pins: `obligations/vector_at_partial_function`,
  `drivers/implRev4` ("do not count local by-sorry bounds obligations as
  proof discharge").
- [ ] **Whole-module translation of polymorphic indexing comprehensions
  rejects at `Prelude::Either@core` (found 2026-07-12; blocks
  saw-lean-example `write_lean_cryptol_module "rev.cry"`).** With symbolic
  `fin n`, the `[0 .. < n]` enumeration/indexing machinery reaches the
  Either recursor with a raw result demanded from an Except-wrapped
  scrutinee — the same recursor-convention hole as the parked
  `Prelude::Stream@core` pair, and material to that parked decision.
  Monomorphic instances translate fine (the demo's `implRev4` term and the
  litmus's `Either.rec` sign-split emit). Polymorphic `reverse` (specRev)
  also translates; the comprehension is the trigger. Pinned:
  `saw-boundary/polymorphic_seq_module_rejection`.
- [ ] **Slice 3** (3a–3d) — push position through `Pi`/`Lambda`/`let`; demote
  `shouldWrapBinder`, `isVariableHead`, `natValueResult`, `phaseBetaResultShape`
  from position authorities to convention-internal helpers.
  - [x] 3a — `ExpectFunctionPosition` carries `Maybe FunctionConvention`
    (arg positions + result position); `translateLambdaAtConvention` +
    `translateBinderAt` consume it; producers: MkStream index functions
    (`translateFunctionWithWrappedResult`) and non-dependent `UseArgFunction`
    helper lambdas (`translateFunctionToWrappedFormal`) declare conventions
    once (predicates now convention-internal at those sites). Dependent
    (`typeIxs ≠ []`) and sort-binder lambdas stay legacy until 3b.
    Byte-identical to baseline; new path live (traced on
    `obligations/mkstream_total`).
  - [x] 3b — dependent binders join the convention path: index binders declare
    `ExpectRaw RawIndexPosition`, sort-typed type binders `ExpectRaw
    RawTypePosition` (driving the legacy `SortBinderAsType` universe mode
    inside `translateBinderAt`); both producers drop their non-dependent
    guards, so every lambda they accept goes through
    `translateLambdaAtConvention`. Byte-identical across the full driver
    corpus (~150 rows incl. llvm/salsa20 all golden-green). The dependent
    positions are correct-by-parity but likely dormant until Slice 4 routes
    more callee arguments through conventions — most helper function formals
    are non-dependent by construction; the dependent family mostly flows
    through the still-legacy generic Lambda case. (3b corpus trace sweep:
    33 live conventions, all non-dependent, zero inconsistent.)
  - [x] 3d — let-sharing threads the demanded position:
    `translateTermLetAt` (legacy entry = `Nothing` specialization); the body
    inherits the surrounding convention's declared result position;
    convention consumers pass it. Shared-RHS Γ records and loud
    incompatible-position failure were already in place from Slices 1–2;
    emitting separate bindings for position-polymorphic shares is deferred
    until a fixture demands it.
  - [x] 3c — recursor motives at a declared `MotiveConvention` (per-binder
    positions: indices `RawIndexPosition`, scrutinee
    `StructuralRecursorFieldPosition`; result mode drives the type-level
    `wrapExcept`, per calculus §Recursors' "motive binder/result position"
    fields). `translateMotiveAtConvention` replaces the where-local
    `translateRecursorMotive` and its blanket `skipBinderWrap True` — one
    flag site deleted. Byte-identical incl. re-emitted Stream.rec /
    RecordType.rec driver rows; motive trace live on `conformance_stream`.
- [x] **Slice 4** (4a–4c, see plan doc) — real callee conventions for every
  callee; retire `CalleeTransitional`; decompose `originalDispatchWithShape`
  into a convention interpreter + table. COMPLETE 2026-07-10. 4c closing
  steps: function-value conventions swapped in (oracle-proven;
  `applyKnownFunctionWithShape`'s per-arg peel deleted, result-type peel
  documented convention-internal); proof-primitive contracts declare true
  slot roles from the SAWCore signatures (raw-logical interpretation
  unchanged); `CalleeTransitional` retired BY DELETION (the old
  `CalleeConvention` enum was vestigial — only its raw-logical arm was ever
  consumed; the real classifier is the declarative guard chain over the
  contract tables with declared `ArgMode` slots, now documented as such);
  `bindingShapeOfType` documented as a convention-internal self-mirror
  (legal inputs: types the calling function itself just built);
  `UseArgShape` stays table-local (its interpreter already binds wrapped
  actuals at raw slots — no 4a hazard).
  - [x] 4a — calculus `ArgMode`/`ResultMode` vocabulary as data; checked-
    application contracts re-expressed (`CheckedArgRaw` split into true
    `IndexArg`/`TypeArg` slots per the helpers' Lean signatures); the
    interpreter returns per-actual verdicts and a *wrapped* actual at an
    `IndexArg` slot is sequenced through an error-preserving `Bind.bind`
    with the bound RAW variable consumed by both the bounds proposition and
    the checked helper (application order). **Fixes the live specimen**
    `workflows/llvm_chacha20_core_verify` (previously: wrapped shared index
    passed raw into `LT.lt`/`atWithProof_checkedM`, did not elaborate) —
    now green end-to-end; goldens refreshed to the corrected emission.
    New fast fence row `obligations/vector_at_runtime_index` pins the
    bind-chain shape. Everything else byte-identical (only the specimen row
    changed, diff reviewed). First reviewed-diff (non-empty) fence of the
    migration.
  - [x] 4b step 1 — wrapped partial-op contracts lifted to `ArgMode`
    (widths `IndexArg` with the bind protection); shared
    `lowerProofCarryingActuals` lowering. Proof-primitive relabel deferred
    to 4c (raw-logical translation, no behavioral content in a relabel).
  - [x] 4b steps 2–3 — the two-oracle inert step proved the derived
    convention equivalent to the legacy bind plan across the whole corpus
    (oracle 2 rejected the first source-based classifier candidate on the
    smoketest: value-domain instantiation ≠ wrapped-representation
    instantiation; corrected to Pi-instantiation-only), then the swap:
    `phaseBetaArgModesFor` over source actuals is authoritative on the
    full-application path. Legacy plan + the emitted-type predicate remain
    ONLY on the eta/partial path and `PartialOpRaw`, quarantined.
  - [x] 4b step 4 — legacy bind plan DELETED; conventions drive all paths
    (eta/partial-application, `etaExpandWrappedFunctionResult`,
    `PartialOpRaw`). `polymorphicFormalInstantiatedExpected` (the last
    emitted-Lean-TERM inspection) deleted with it; Num reclassified
    `TypeArg` (exactly-legacy never-bind). Two type-classification
    self-mirrors remain (`bindingShapeOfType`, `applyKnownFunctionWithShape`
    peel) — 4c demotion targets. Byte-identical corpus-wide.
  - [x] 4b fixture item RECLASSIFIED: the 3b dependent-lambda conventions
    are structurally UNREACHABLE today, not dormant — the only function
    slots (`foldr`/`foldl` formals `a → b → b`, MkStream `Nat → a`) are
    non-dependent by the helpers' types, so SAWCore's typechecker rejects
    any dependent lambda upstream of the producers. The fixture rides the
    first dependent `FunctionArg` convention (4c/Slice-5-era work).
  - [x] **Deliberate emission-quality debts — COMPLETE 2026-07-10
    (commits `4cf6e8106` part 1, `7a566afa6` part 2, `a899c6ccd` part 3).
    Original rationale (user-reviewed; parity-preserved on purpose through
    Slice 5 so the oracle baselines stayed sharp through the equality
    work; REORDERED before Slice 6 after the Slice 5 design review, with
    user): (a) source of the false raw-mode production records that forced
    two mode-guard workarounds; (b) Slice 6.1's recursor classification
    consumes exactly these inputs; (c) the equality subject rule rests on
    record truthfulness. OUTCOME: all three held. Part 3 (not in the
    original list — the false-record mechanism turned out to be raw-mode
    stamping with `phaseBetaResultShape`, a third site, not the two debts
    themselves): `rawModeResultShape` stamps raw-mode applications
    truthfully (landed emission-inert, corpus byte-identical), after which
    BOTH mode-guards collapsed byte-identically — `lowerRawLogicalCallee`
    is the single mode-uniform pipeline (`lowerRawLogicalCalleeRawMode`
    deleted), unsafeAssert's raw-mode arm deleted, and
    `equalityPropositionAtSubjectRep` (the declared-rep entry point)
    deleted with it: no surround declares a rep anymore — every equality
    surround classifies from the operands' production records. The
    collapse being byte-identical INCLUDING the auto-emitted raw prelude
    is the proof the operand-domain rule is mode-uniform. Records are now
    the translator's single source of truth going into Slice 6. Remaining
    known-false stamp: none found; the recursor-convention stamp at
    `recursorConvention`/`classifyRecursorResult` was Slice 6 territory
    and was left untouched (since reworked by Slice 6.1, `2000c7719`:
    `classifyRecursorResult` deleted, the convention now derives from the
    declared `recursorMotiveResultPosition`). Each fixed debt lived at ONE marked
    chokepoint (grep SUSPECT in Term.hs — all markers now resolved):**
    - [x] `phaseBetaBindFromMode`: `RawValueArg` bound RAW actuals too
      (pure-lift-then-bind — identity but monadic noise). FIXED 2026-07-10:
      bind-iff-wrapped (`RawValueArg -> actualWrapped`, same discipline as
      `IndexArg`). Eta paths unaffected by construction (they DECLARE
      missing formals wrapped, so `actualWrapped` is True there). Emission
      diff reviewed: 13 artifacts (12 differential + stream_scanl_totality),
      every hunk a disappearing `Bind.bind (Pure.pure <raw>) (fun v_i => …)`
      splice plus fresh-name prime shifts; no wrapped actual lost its bind;
      NO driver artifacts changed (no golden refresh needed). Differential
      rows verify the changed emissions end-to-end (Lean evaluation ==
      SAW evaluation); stream_scanl_totality elaborated explicitly.
      Smoketest 54/54 (one substring assertion switched to squashed —
      shorter output moved a line-wrap point), conformance 192 OK exit 0,
      snapshot re-baselined (317).
    - [x] `phaseBetaArgModesFor`: a var-headed formal falling past the
      Pi-instantiation lookup was ASSUMED value-domain. FIXED 2026-07-10:
      instantiation-directed modes — `varHeadedInstantiation` looks up the
      supplied type actual for a bare-parameter formal type, and
      `instantiationMode` classifies it by the SAME domain analysis
      `modeFor` applies to concrete formal types (Pi → `FunctionArg
      Nothing`, Nat → IndexArg, Num/sort → TypeArg, Eq → PropositionArg,
      value-domain → RawValueArg). Subsumes and deletes
      `polymorphicFormalInstantiatedExpectedSrc` (its RuntimeArg is
      behaviorally identical to `FunctionArg Nothing` at every consumer).
      The value-domain RESIDUAL survives only where the instantiation is
      genuinely unavailable (type actual not supplied; var-headed
      APPLICATION formal types) — sound at supplied positions post
      bind-iff-wrapped (the actual's recorded shape directs the bind;
      functions deliver structurally, never wrapped); an assumption only
      for eta-declared MISSING formals in partial applications. The
      dependent `FunctionArg (Just conv)` machinery was NOT needed:
      external raw-formal targets take the translated Pi type actual
      as-is, and dependent function slots remain structurally unreachable
      (see the 4b reclassification above). Corpus byte-identical (the
      directed cases only diverge at missing positions with no corpus
      witness). Coverage: smoketest "partial ctor eta formals are
      instantiation-directed" (partial `PairValue (Bool -> Bool) Bool`:
      function-slot eta formal splices raw, value-slot binds — top-level
      partial applications never elaborate, so this pin cannot be an
      obligations row) + obligations/polymorphic_inst_function_slot (full
      application: lambda delivers structurally at the phase-β function
      carrier, elaborates). Smoketest 55/55, conformance 193 OK exit 0,
      snapshot re-baselined (318).
    The two-family asymmetry itself (raw-formal external targets with
    call-site sequencing vs wrapped-formal translated function values) is
    NOT a debt — it is forced: propositions need raw operands; partial
    application over computed prefixes needs effectful closure interfaces.
  - Original 4b design notes from the 2026-07-09 analysis (implemented):
    (i) the convention derivation must take the SUPPLIED TYPE ACTUALS, not
    just the callee Pi type — `argumentBindPlanFromWrapped`'s
    `paramActualAlreadyExpected` handles polymorphic formals by inspecting
    the emitted Lean type of the instantiating actual
    (`isExceptStringType`/`isLeanPiType`), which is the last
    emitted-AST-inspection class in the translator and must become a
    declared instantiation lookup; (ii) legacy bind semantics: value
    formals bind ALWAYS (raw actuals pure-lift then bind — uniform
    chains), Nat formals bind iff the actual is wrapped (IndexArg
    semantics), typeIx/sort/Eq/Pi/Num formals never bind; (iii) migration
    path: implement `phaseBetaArgModesFor fty typeActuals` PURE, first
    land it behavior-inert with a loud equivalence assert against
    `argumentBindPlan` across the corpus (Slice-0 oracle pattern), then
    swap and delete the legacy plan; (iv) prefix partial application and
    the dependent higher-order fixture (3b dormancy) ride this step.
- [x] **Slice 5** (5a–5c, see plan doc) — equality subject representation &
  `Eq.rec` proof transport declared (never inferred from type names). The six
  load-bearing rows (`obligations/proof_add_nat_assoc`, `proof_eq_nat_add_0`,
  `proof_eq_nat_add_s`, `proof_eq_nat_add_comm`, `proof_equal_nat_to_eq_nat`,
  `proof_transport_runtime_subject`) were already green entering the slice —
  they are the fence; wrapped-value equality must not regress.
  - [x] 5a (2026-07-10) — standalone-proposition convention named, documented,
    and traced (`standaloneEqualitySubjectRep`, `[subjectRep]` trace lines);
    `equalityPropositionAtSubjectRep` is the declared-surround entry point
    (unsafeAssert = raw); byte-identical to baseline.
  - [x] 5b (2026-07-10) — full `Eq.rec` field set as `EqRecConvention`
    (operand ρ_eq, carrier universe class, motive binder/result positions via
    `MotiveConvention`, branch position, proof position, result shape),
    constructed once by `eqRecConventionForStandalone`, consumed by the
    lowering with no operand re-inspection. All-raw subset byte-identical
    (raw-mode motive interpretation is the declared interpreter for
    `MotiveComputesRawType`). NEW capability: runtime-subject `Eq__rec`
    transports (previously blanket-rejected) — the wrapped carrier flows
    consistently into the proof binder's proposition, the motive's subject
    binder and inner proposition (consistency BY CONSTRUCTION: the wrapped
    `y` binder in Γ drives the inner standalone classification), the
    `Pure.pure`-lifted branch, and the wrapped result. Pinned by
    `obligations/proof_transport_runtime_eqrec` (elaborates in Lean,
    `#print axioms` clean). A proof produced at a mismatched rep fails
    loudly at Lean elaboration — the carrier types differ; nothing coerces.
  - [x] 5-followup (2026-07-10, design review): the operand-domain rule is
    the UNIVERSAL semantic definition of ρ_eq, not a standalone-case
    fallback — a surround may only "declare" ρ_eq when its own slot
    contracts pin the operand domain. unsafeAssert's did not: its
    unconditional declared-raw dropped effect structure over effectful
    operands and produced an obligation that could not stand at the goal's
    wrapped carrier. It now classifies through
    `standaloneEqualitySubjectRep` in ambient mode (raw pipeline in raw
    mode); byte-identical for all pure-operand emissions; pinned by
    `obligations/unsafe_assert_effectful_subject` (faithful wrapped
    obligation, discharged by `rfl` in the probe). (The raw-mode arm
    described here was since collapsed by the debts slice part 3 —
    classification is now mode-uniform.)
  - [x] 5c (2026-07-10) — function-carrier equality decided:
    `EqualitySubjectRawFunction` with the carrier translated in the CURRENT
    mode — raw logical content compares functions at the raw `a -> b` it
    quantifies over (`inverse_eta_rule`), ambient Phase-β content at the
    translated effectful type (`Except String Bool -> Except String Bool`,
    pinned by `obligations/proof_fn_carrier_eq_ambient`, axiom-clean); a
    wrapped operand mixed with a function subject rejects (carrier not
    uniquely determined). ALSO: raw-translation-mode raw-logical callees now
    interpret through the raw pipeline (`lowerRawLogicalCalleeRawMode`) —
    shape records of raw-mode translations are not consulted, because the
    documented 4c var-headed debt stamps some raw-mode applications wrapped
    and a false record was steering `coerce__def_trans`'s carrier into
    `Except String` around raw terms. Byte-identical for every pre-existing
    artifact; `drivers/sawcore_prelude_auto_emit` un-rejected (golden
    refreshed per-hunk: only the `Eq__rec` → `@Eq.rec` head changed; full
    prelude elaborates with zero errors). (`lowerRawLogicalCalleeRawMode`
    was since deleted by the debts slice part 3: truthful raw-mode records
    made the mode-uniform pipeline reduce to it byte-identically.)

  **Slice 5 exit fence (2026-07-10):** smoketest 54/54; conformance exit 0
  (191 OK, +2 fixture rows over the slice); the six load-bearing rows green;
  both new fixtures' artifacts elaborate and depend on no axioms; baseline
  snapshot 316 artifacts (313 untouched byte-for-byte across the slice + 2
  new fixture emissions + the un-rejected auto-emitted prelude).
- [x] **Slice 6** — recursors as a position/callee instance; close the
  `@Foo.rec`-by-name constructor-order trust hole (bridges to the separately
  tracked direct-recursor / `PosRep` work in
  `doc/archive/2026-07-03_direct-recursor-semantics-design.md`).
  **COMPLETE (2026-07-10, commits `2000c7719` + `133f2cd69`).**
  - **6.1 (`2000c7719`, emission-inert — corpus byte-identical):** the
    recursor convention DERIVES from a declared motive result position.
    New shared classifier `recursorMotiveResultPosition` (same domain
    analysis as the argument-mode tables; two declared refinements:
    non-Prop Nat elimination computes a runtime value, var-headed type
    families stay raw) and `recursorMotiveFunctionConvention` (binder
    positions from `functionConventionValueSlot`, result position
    mirroring the Pi translator's body-wrap rule — the type the emitted
    call actually inhabits). `RecursorConvention` gains
    `recMotiveResultPosition`; `recResultMode`/`recFinalShape` derive
    from it; `motiveConventionFor` consumes the position (Bool arg
    gone); `classifyRecursorResult`/`recursorDirectResultIsValue`
    deleted; `recursorPostArgs` and
    `recursorFunctionResultCanPropagate` read the declared convention;
    the recursor's `phaseBetaResultShape` call is gone (one fewer
    standalone authority ahead of Slice 7).
  - **6.2 (`133f2cd69`, emission-changing — additive, diffs reviewed):**
    Lean-checked constructor-order assertions. Support-library command
    `saw_ctor_order Foo [Foo.A, …]` (CryptolToLean/SAWCoreCtorOrder.lean)
    fails elaboration unless the inductive declares exactly those
    constructors in that order; positive + `#guard_msgs` negative
    self-tests run at every lake build. The translator records a
    `CtorOrderAssertion` decl (from `recursorCtorOrder`, fully-qualified
    names — command-level resolution can't type-disambiguate
    core-colliding short names like `Stream`/`Either`) whenever it emits
    a recursor head; both drift directions (Lean library reorder, SAWCore
    prelude reorder) now fail loudly. SAWModule's bridge drains
    `topLevelDeclarations` instead of dropping them. `Eq.rec` is out of
    scope by design (declared `EqRecConvention` onto Lean-core `Eq`).
    Driver-golden refresh trued up 11 recursor drivers (all pass test
    mode), also picking up the debts-slice emission those goldens had
    missed. Six gated families (Nat/Pos/Z/Bool/AccessibleNat/
    AccessiblePos) stay rejected.

  **Slice 6 exit fence (2026-07-10):** lake build green (incl.
  self-tests); smoketest 55/55; conformance 193 OK exit 0 with
  assertions elaborating in every recursor row;
  `recursor_raw_scrutinee_effectful_value` pins the assertion emission;
  snapshot re-baselined at 318 artifacts, diff clean.
- [x] **Slice 7** — delete the demoted heuristics; add an anti-regression lint
  (no `bindingShapeOfTerm`, no `CalleeTransitional`, no emitted-AST shape
  inspection); sync `STATUS.md`, the Priority 2 items below, and the calculus
  doc's "Current Rough Edges".
  **COMPLETE (2026-07-11).** The value-domain result rule centralized in
  `phaseBetaResultIsValue` (single authority; the trio
  `shouldWrapBinder ret || isVariableHead ret || natValueResult fty` was
  restated at 7 sites — application full/eta paths, partial-op
  contracts, `etaExpandWrappedFunctionResult`, the Pi body wrap, the
  recursor motive convention — all now read the one function;
  corpus byte-identical). `natValueResult` demoted to a
  convention-internal predicate of that rule; `phaseBetaResultShape`
  reduced to the documented result-shape stamp of the ordinary Phase-β
  convention; `shouldWrapBinder`/`isVariableHead`/
  `functionConventionValueSlot`/`functionConventionResultIsValue`
  carry convention-internal doc contracts. `bindingShapeOfTerm`,
  emitted-TERM inspection, and `CalleeTransitional` confirmed gone.
  Anti-regression lint added to the smoketest (2 cases): a
  forbidden-name check over ten deleted heuristics (comment tombstones
  exempt; validated to FIRE via a string-literal canary) and ceiling
  gates on the allow-listed emitted-TYPE self-mirrors
  (`bindingShapeOfType` 7, `isExceptStringType` 5, `peelLeanPiTypes`
  6 non-comment lines — do not add consumers; the
  `applyKnownFunctionWithShape` result peel needs its own inert-oracle
  step to demote, NOT attempted here because the source mirror can
  diverge under `inRecursorCaseBinder`-suppressed type wraps).
  `STATUS.md` rewritten (was stale since 2026-06-28); Priority 2 items
  "promote design to explicit data types", "centralize adaptation",
  "replace transitional local policy" marked complete; the calculus doc
  gained an "Implementation Status (2026-07-11)" section recording that
  the calculus IS the implementation and the remaining rough edges.
  Exit fence: smoketest 57/57 (55 + 2 lint), conformance 193 OK exit 0,
  emitted Lean byte-identical to the slice0 baseline.

Guardrails (from the calculus §Stop Conditions): no new Lean axioms; no `sorry`
as evidence; never classify by fixture name or emitted Lean AST; never use
`DefPreserveRaw` as a use-site proxy; when a slice cannot classify a case,
reject and pin a fixture rather than widen a heuristic.

