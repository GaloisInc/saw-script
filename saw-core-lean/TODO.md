# saw-core-lean — project TODO

This is the WORKING document: what is open, in priority order.
What the backend is and does today: `STATUS.md`. How it works:
`doc/architecture.md` and `doc/2026-07-02_position-callee-calculus.md`.
The complete 0.01/0.02 buildout record — every completed item with
its full execution rider — is frozen verbatim at
`doc/archive/2026-07-24_todo-execution-record.md`; per-decision and
per-audit indexes are `doc/decision-log.md` and
`doc/audit-history.md`.

## Goal

`saw-core-lean` exists to discharge SAW proof obligations in Lean 4's
kernel — a proof backend filling the same slot as a solver backend,
with a kernel-checked, inspectable, replayable artifact. Translation
of Cryptol/SAWCore to Lean is the means, never the product.
Soundness is absolute: the emitted Lean statement must faithfully
express the SAW obligation, and every input outside the supported
fragment fails LOUDLY at translation. No silent divergence, ever.

## Release gate (0.02 → release)

- [ ] **Pre-release soundness review** (release gate, added
  2026-07-17; scope raised 2026-07-21, user request): a
  whole-project soundness review by MULTIPLE INDEPENDENT reviewers
  (fresh contexts, never the implementing session), each assigned a
  distinct part of the trust chain, searching for unsound-acceptance
  paths — cases where a Lean proof succeeds while the SAW statement
  is false or has different semantics — with findings independently
  cross-checked before landing. Scope: translator, support library,
  harness, replay kernel, trust-tier machinery, docs-vs-behavior
  honesty. Working assumption: a defect exists until the surface is
  shown sound. Minimum probe classes (full checklists in the
  archived record and `.tmp/audit-goal.md`, the calibrated reviewer
  prompt): replay acceptance checks (allowlist name variants,
  shadowing, staging-path confusion, toolchain substitution),
  emission seams (the six-bug syntactic-under-approximation
  pattern), harness vacuity (each gate must have a mutation it
  catches), tier containment (no path admits native axioms on a
  strict-tier row), and differential stress on divergence-prone
  inputs. Every finding lands as a pinned regression row or a
  documented reject; the report is a doc/ artifact. Prior art:
  `doc/2026-07-21_soundness-review.md` (three surfaces, found F1),
  `doc/2026-07-23_fidelity-review.md` (library realizations, found
  the bvToInt class).
  **STATUS 2026-07-24: the panel RAN** (six Opus reviewers, one lane
  each; report = `doc/2026-07-24_soundness-audit.md`). Verdict: one
  CRITICAL (R-1, replay completed-outline goal binding) — **FIXED
  same day** with red-before/green-after pins in both consumers.
  V-H1 (negative-probe diagnostic pins — found four probes ALREADY
  vacuous, recalibrated as deletion pins), V-H2/V-H3 (obligation
  harness guards), LB-2/TIER-1/DOC-1 (doc honesty) — all FIXED
  2026-07-24. Still OPEN from that audit: LB-1 (raw fix contract) —
  **now superseded by S-2 below, which supplies the witness proving
  it reachable** — and SEAMS-D3, **now SETTLED in the affirmative by
  F-2 below**.
  **A SECOND panel then ran the same day** and found R-1 was one
  instance of a class rather than the class: report
  `doc/2026-07-24_soundness-audit-2.md`, findings tracked in the
  section below. Three further CRITICALs, two demonstrated
  end-to-end. The release gate is NOT met until those clear.
## Release gate — second audit findings (2026-07-24)

A SECOND independent six-lane audit ran the same day
(`doc/2026-07-24_soundness-audit-2.md`), after the first audit's R-1
fix landed. It found that R-1 was one instance of a class, not the
class: **three further CRITICALs, two of them demonstrated
end-to-end against the shipped trust kernel.** Items below are
verbatim-traceable to that report; `[V]` marks claims re-verified
independently in-session (2026-07-24, read-only).

### Blocks release

**Status 2026-07-25: A-1, A-2, A-5, A-9, S-1, S-2, F-5 and LIB-2 are
CLOSED** (plus A-6, A-7, A-3, RK-5, RK-7, HELP-1 and the four
mechanical categories C1–C4). **LIB-1 is the one remaining
confirmed soundness defect**; it is a CARRIER defect, not a gate or
contract defect, so no trust-kernel work reaches it — see its row
below.

- [x] **A-1 (CRITICAL) — CLOSED 2026-07-25** (commit fa842349b).
  `notation` capture of the binding probe. A user `proof.lean` containing `notation "goal" => True`
  makes the checker's `#check (goal_closed : goal)` probe resolve
  `goal` in the USER's token table: `CHECK-OK` on a proof of `True`
  against a false obligation. Live on runtime replay AND the CI
  harness; additionally defeats the in-statement `by sorry`
  obligation detection (the captured closer's type never mentions
  `goal`, so `#print axioms` never traverses it). Fix = BOTH
  (a) ban syntax-declaring commands in proof-side files
  (`notation|syntax|infix|infixl|infixr|prefix|postfix|declare_syntax_cat|binder_predicate|unif_hint|export`)
  in `proof-source-lint.awk:168` — measured cost zero across all 119
  proof-side files — and (b) A-5's kernel-checked binding theorem.
  **A probe rename does NOT work** (verified in-report: notation
  atoms are arbitrary strings, so `_root_.goal` and `«goal»` are
  capturable too). *Standing caution: the report's §A-5 claims its
  binding theorem alone blocks A-1; in-session analysis disputes
  this (the notation captures the binding theorem identically) —
  settle by experiment, do NOT drop the lint half on that claim.*
- [x] **A-5 (CRITICAL) — CLOSED 2026-07-25** (commit 389a55ec9).
  The probe accepted a coercion and the audit inspected the wrong
  declaration. `#check (goal : …)`
  type-ascription inserts coercions, so a user `instance : CoeT True
  goal_closed goal := ⟨hidden⟩` makes the probe pass via `def hidden`
  — which the closer awk (`theorem|lemma` only) never audits.
  Result: `native_decide` trust admitted on a STRICT-tier row. Fix
  (verified effective in-report): replace the `#check` with a real
  kernel-checked declaration and audit IT —
  `theorem __replay_binding : goal := goal_closed` +
  `#print axioms __replay_binding`.
- [ ] **S-1 (CRITICAL) — the Class-F / Class-S productivity
  obligations are ERASABLE on the completed-outline path** (the only
  path that can accept them). `[V]` `saw_stream_realize`'s body is
  `Pure.pure (saw_stream_unfold α x0 step)` — it mentions neither
  `mkfn` nor `_h`, while its own docstring claims "the proof argument
  is consumed so an undischarged obligation is loud". `[V]`
  `saw_fix_bounded_choose` uses `Classical.choice h.seed`
  (Prop-typed ⇒ proof-irrelevant ⇒ erasable); contrast
  `saw_mkStream_choose`, which uses `Classical.choose` (carries the
  predicate as a type-level implicit ⇒ binding). So a completed
  outline may write the reduct directly, never stating
  `total`/`lookback`/`faithful`, and drift-`rfl` passes clean.
  10+ tracked `proofs/*/completed.lean` rows sit on this path and
  no pin exists. **FIX-SEAM ⇒ pause rule applies: discuss before
  touching the recognizer/realization surface.** Verify first — the
  audit lane could not execute the defeq reductions.

### High

- [x] **A-2 (HIGH) — FULLY CLOSED 2026-07-25.** Checker half landed
  2026-07-24 (75c2acfc6, C1): goal presence is now derived from the
  authority and is an INVARIANT, so `has_goal_def=0` cannot silently
  disable the binding gate on either replay path. The EMITTER half
  landed today: goal emission now refuses a non-empty `universeVars`
  at translation time (`UnrepresentableGoalShape`), so the shape is
  never produced in the first place rather than merely failing
  loudly downstream. Pinned by
  `saw-boundary/goal_sort_binder_rejection/sort1_binder`. Original
  finding: `[V]` a goal rendered `noncomputable def goal.{u0} :`
  missed the detection regex ⇒ the binding gate disappeared ⇒ a
  `proof.lean` that never mentions the goal was admitted; trigger
  REACHABLE via `parse_core` and no `writeLeanProp` telescope pin
  fires.
- [x] **A-9 (HIGH) — CLOSED BY CONSTRUCTION 2026-07-25.** The
  `goal_holds` stub is still built from the bare `nameStr`
  (`Lean.hs`), but it can no longer drop anything: A-2's emitter gate
  refuses any goal that allocates a universe variable, so a goal
  reaching the stub has NO universe binders to drop. Recorded here
  rather than "fixed" because the dependency is real — reopening the
  universe gate reopens A-9, and the comment at the stub site says
  so.
- [x] **A-6 (HIGH) — CLOSED 2026-07-25** (fa842349b). `«debug».skipKernelTC` evaded the source lint
  (`proof-source-lint.awk:170` matches `debug\.` literally; Lean
  treats the escaped component as the same `Name`). Kernel type
  checking off for the whole file = the Lean kernel leaves the
  trusted base. One-line fix: `gsub(/[«»]/, "", out)` before the
  denylist match, which also hardens every other rule against
  `«axiom»`-style spellings.
- [ ] **LIB-1 / D-1 (HIGH) — the wrapped-vector carrier EQUATES
  computations SAW distinguishes** (found independently by two
  lanes; the audit's most significant translator-side finding).
  SAW's vectors are element-lazy (`genOp` builds delayed thunks;
  `atWithDefaultOp` forces only the selected one), but the Lean
  carrier `Except String (Vec n T')` cannot represent "error in one
  slot, good values elsewhere" — `genWithBoundsM` = `Vector.ofFnM`
  sequences and short-circuits, denotationally. The adaptation is
  NON-INJECTIVE and the collapsed value appears on BOTH sides of
  emitted equations, so a SAW-FALSE equation closes by `rfl` in
  Lean. Same class, lower reach: `genM`, `vecSequenceM`,
  `atRuntimeCheckedM`, `foldrM`/`foldlM`, `sawLet`. NOT affected
  (each checked): `iteM`, accumulators, `atWithDefaultM`.
  **Reachability SETTLED 2026-07-25 (affirmative).** Scratch witness:
  SAW gives `7` where Lean gives `9`, and Lean proves them EQUAL with
  only `[propext, Quot.sound]` — a SAW-false equation closing in a
  clean kernel. The witness is scratch-only; **the row is still
  missing** (template `differential/error_unreachable/test.saw`) and
  writing it is the first action.

  **Character (2026-07-25): this is a CARRIER defect**, and that is
  why it survived a day of trust-kernel work. A-1/A-2/A-5/R-1 were
  GATE defects (the checker failed to look); S-1/S-2/LIB-2 were
  CONTRACT defects (the emitted obligation was not binding). Both
  classes are reachable from the replay kernel. LIB-1 is neither: the
  emitted statement is well-formed, genuinely proved, kernel-checked
  and allowlist-clean — and false in SAW. No gate can catch it,
  because there is nothing wrong with the proof.

  Options weighed with the user:
  (a) move `Except` INSIDE the element (`Vec n (Except String T')`) —
      principled, but a 0.03-scale rewrite of the value convention;
  (b) REJECT element bodies that can throw — measured zero blast
      radius on `gen`;
  (c) document only — excluded by the "must not ship soundness bugs"
      rule.
  Recommendation: **(b) now, (a) as successor** (same shape as S-1's
  interim/successor split). Three things must settle first:
  1. **Scope.** Only `gen` is measured. `genM`, `vecSequenceM`,
     `atRuntimeCheckedM`, `foldrM`/`foldlM` and `sawLet` are
     UNMEASURED. `sawLet` is a distinct instance, not a variant: SAW
     beta-reduces and DISCARDS a throwing `x`, while Lean propagates
     it.
  2. **Conservatism.** "Can this body throw" is undecidable, so (b)
     must reject any body that *can*.
  3. **Product posture.** Unlike LIB-2 (parse_core-only), (b) may
     bite real user Cryptol: `error` inside a sequence comprehension
     is a plausible defensive idiom. That is a call for the user, not
     the translator.
  Measure each surface with the suite before committing to a
  rejection count — the LIB-2 estimate was wrong twice, in both
  directions.
- [x] **F-5 (HIGH if reachable) — CLOSED 2026-07-25.** Resolved the
  same way as A-2, and together with it as the row required: goal
  emission refuses a sort-typed binder outright rather than emitting
  a narrower one. The audit's other option (emit `Sort u` for sort-0
  binders) was rejected — it allocates a universe variable and so
  collides head-on with the A-2 gate; "a goal telescope may not
  quantify over a sort" is the one rule that discharges both. The
  scan (`leanSortBinders`) walks the WHOLE emitted term, not just
  the Pi spine, because the narrowing is a property of the binder:
  `(f : (a : sort 0) -> …) -> …` hides one where a spine walk stops.
  `Prop` binders are deliberately NOT refused — SAWCore `Prop` maps
  to Lean `Prop` with no cumulativity gap. Pinned by
  `saw-boundary/goal_sort_binder_rejection/sort0_binder`. Original
  finding: SAWCore admits `Prop ≤ sort 0` cumulativity and applies it
  as subsumption, so a SAW binder `(a : sort 0)` can be instantiated
  at a proposition; Lean 4 has no term cumulativity, so the emitted
  goal was strictly WEAKER. Zero corpus hits (specialization
  monomorphizes goals).

### Medium

- [x] **S-2 — CLOSED 2026-07-25.** Raw-position fixes now REJECT at
  translation (`lowerFixProofObligation` DELETED, not merely bypassed —
  dead code emitting an unsound contract is one re-wire from returning).
  Cost: a REAL Cryptol feature deferral (chacha20 iterate/iround),
  gapped as `differential/cryptol_chacha20_*`; restoration = the 0.03
  productivity-gated raw contract. Original finding:
  dischargeable** (upgrades the first audit's LB-1 from "latent,
  zero corpus uses"). Witness: `parse_core "fix Nat (\n -> mulNat n
  0)"` routes `FixUnrecognized` → `shouldWrapBinder Nat = False` →
  `lowerFixProofObligation`; the obligation is provable in three
  tokens (`⟨0, rfl, fun y h => h.symm⟩`) while SAW's meaning is ⊥.
  **Not fixable by hardening a checker** — the contract is
  extensional and cannot observe divergence. Also recorded: ordinary
  recursive Cryptol functions escape this only ACCIDENTALLY (the
  constant-error family is a fixed point of bind-sequenced bodies,
  so uniqueness fails for divergent shapes) — protection that does
  not extend to `DNat`/`DRawProp`/`DRawType`. FIX-SEAM ⇒ pause rule.
- [x] **LIB-2 — CLOSED 2026-07-25.** Contracts removed so the
  pre-existing `SpecialTreatment` rejects finally fire — they had
  been DEAD CODE, shadowed by the contract path. Cost: NO Cryptol
  capability (verified: reachable only from hand-written SAWCore);
  13 probe/discharge rows gapped, 4 stale goldens retired.
  Principled restoration = a genuinely UNINTERPRETED Lean
  realization. Was: `atWithProof`/`genWithProof`/
  `updWithProof`/`sliceWithProof`/`updSliceWithProof` are declared
  `primitive` with no body and have zero implementations anywhere in
  SAW; their only semantics is their type. The Lean helpers give
  them values, so the Lean statement is strictly WEAKER than the SAW
  obligation (which must hold for all interpretations). Two
  obligation rows already emit them. Add to the residual-trust
  catalog (currently absent) or gate them the way `IntMod` now is.
- [x] **A-7 — CLOSED 2026-07-25** (fa842349b). Multi-line `@[…]` evaded the attribute rule (`proof-source-lint.awk:171` is per-line by
  construction). Same shape for `csimp`/`extern`; matters for
  native-evaluation trust. Fix: track attribute brackets in the
  lexer state or accumulate across lines.
- [x] **A-3 — CLOSED 2026-07-24** (75c2acfc6, C2). polymorphismResidual was documented as a live gate and does not exist. `[V]` Confirmed absent from every `.hs` in
  the tree (doc-only identifier; the May keep/kill map already
  recorded it dead). Cited as live in `architecture.md:47,124,151,
  169-172`, `README.md:45-46`, `contributing.md:132,239` and —
  critically — **`doc/2026-05-02_residual-trust.md:574`, the trust
  authority itself**, where it backs a universe-soundness argument.
  Also false as written: "translateSort maps every non-Prop SAW sort
  to Lean Type" (only `TypeSort 0` does). The REPLACEMENT machinery
  is sound (lane-core verified no collapse remains and per-binder
  freshness is real) — this is a documentation-faithfulness defect
  in a soundness argument, and it supplies A-2's trigger. *Missed by
  the 2026-07-23 doc-faithfulness pass, which read the claim without
  checking the identifier existed.*
- [x] **HELP-1 — CLOSED 2026-07-25** (389a55ec9). The help text said the discharge path did not exist. `saw-script/src/SAWScript/Interpreter.hs:5303-5307`
  still reads *"Reserved: … NOT AVAILABLE in this release — this
  command currently always fails with a diagnostic. Use
  `offline_lean` (emission-only) and discharge the obligation in
  Lean externally."* — and `:5295`, in `offline_lean`'s own help,
  promises *"SAW-side discharge will arrive as
  `offline_lean_replay`"* in the future tense. Both have been false
  since the replay landing on 2026-07-16 (`Builtins.hs:1528-1611` is
  a complete live implementation: it stages the fresh emission, runs
  the trust kernel, and admits the goal with `LeanReplayEvidence`).
  So for eight days the primary user-facing surface has told users
  the product's central feature is unavailable — a user reading
  `:help offline_lean_replay` would never try it.
  Found 2026-07-24 by an independent agent, AFTER both six-lane
  audits; neither found it. Audit-1's lane-sawside checked that the
  interpreter registrations are pass-through — i.e. it verified the
  WIRING and never read the TEXT.
  Category: C2 (claim without a mechanism) at **inverse polarity** —
  a claim that a mechanism does NOT exist, when it does. The
  `doc-claim-lint.sh` closure does not cover this: it checks that
  identifiers named in maintained `.md` docs resolve, not that
  user-facing behavioural claims are true. See the C2 note in
  `doc/2026-07-24_semantic-trust-kernel-plan.md` for the proposed
  second half (a stale-promise lint over prim help text: every
  "not yet" / "will arrive" / "NOT AVAILABLE" / "always fails"
  claim must be re-justified, because nothing breaks when such a
  claim becomes false).
  Fix: rewrite both help texts to describe what replay actually
  does and what it requires (a `proofDir` with `proof.lean`, and
  optionally `completed.lean`), and state the strict-tier admission
  posture (TIER-1).
- [x] **RK-5 — CLOSED 2026-07-25** (389a55ec9). The CI harness bound inside the user's own module.
  `lean-proof-test.sh` appends its checks to a COPY of the row's
  `proof.lean`, so both names resolve in the row author's scope: a
  row that omits `import Emitted` and defines its own `goal` passes
  everything. Accidental-miss class (an honest row that forgets the
  import silently stops being checked) AND it means the suite cannot
  catch an A-1/A-5-class regression. Fix: build the checks in a
  separate probe module that imports the emitted artifact. This is
  also genuine consumer drift against the harness's own
  "identical by mechanism, not discipline" claim.
- [x] **F-2 (contracts) — CLOSED 2026-07-25.** SEAMS-D3 was SETTLED
  in the affirmative: type-image collapse was real. `Float` and
  `Double` both bound to `@[reducible] def … := Int × Int` and
  `mkFloat`/`mkDouble` to the same pair constructor, so
  `Eq (sort 0) Float Double`, `Eq Float (mkFloat m e) (mkDouble m e)`
  and `mkFloat`-injectivity were all `rfl`/`decide` in Lean and
  underivable in SAW. Fixed by realizing what SAW actually declares:
  two SEPARATE sealed `opaque` carriers and two uninterpreted
  `opaque` constructors. Rejection (the LIB-2/S-2 treatment) was
  NOT needed — the faithful realization costs nothing, since SAW
  exposes no observer for the components either.
  Cost, deliberate: `obligations/float_mk_*` lost the pair
  observation and now pin emission shape plus a kernel-checked
  equality against the literal constructor application; the old
  observation was reading the bug. Pinned by
  `negative/float_double_collapse` (all three collapsed equations
  must fail with "Not a definitional equality").
  The refuted justification — "SAW has no operations to make this
  binding observable, so any inhabited concrete type is faithful" —
  is corrected in place in `SAWCorePrimitives.lean`. Its error is
  worth keeping in mind for the rest of the table: it conflated **no
  *executable* observer** with **no *equational* observer**, and
  `Eq` is the latter at both the type and the value level.
- [ ] **F-2 (core) — the recursor head is emitted SHORT while its
  ctor-order assertion is emitted QUALIFIED**, so `@Stream.rec` is
  genuinely ambiguous against Lean core's root-scope `Stream` and is
  resolved by overload-by-elaboration; if it ever resolved to the
  core one, the assertion would still pass while checking a
  different inductive.
  **DEFERRED 2026-07-25 with the blast radius measured** — it is not
  the one-line fix the report suggests. Switching the head to
  `translateIdentToQualifiedIdent` (the call the assertion already
  uses) is one line, but it changes emitted output across **15 rows**
  (`@Num.rec` ×39, `@RecordType.rec` ×29, `@Eq.rec` ×15,
  `@Stream.rec` ×9, `@Either.rec`, `@Bool.rec`), and four of those
  are HAND-WRITTEN artifacts, not regenerable goldens:
  `differential/fix_classS_eval/lean-observe.lean`,
  `proofs/cryptol_module_rec_ones`, `proofs/llvm_eq_u128`,
  `proofs/point_shift_property`, `support-lemmas/conformance_stream`.
  Those are written against the emitted names, so this is a change to
  what a USER must write in a discharge — a naming-convention
  decision, not a drive-by. Failure mode meanwhile is LOUD: the
  scrutinee type pins the inductive, so a wrong resolution produces
  an ill-typed application rather than a silently swapped branch.
  Take it with the naming pass (F-6/F-7), not alone.
- [ ] **F-6 / F-7 — name hygiene is delegated to Lean's
  typechecker.** `reservedIdents` omits `Vec Bool Nat Eq Except
  String Pure Bind Num Stream coerce saw_throw_error …`, all of
  which the emitter writes as bare short names into the same file
  (`llvm_fresh_var "Vec"` traces all the way to a shadowing binder).
  Instances fail loudly today, but the disjointness is ACCIDENTAL,
  not structural; Cryptol/SAWCore def names bypass `escapeIdent`
  entirely and land inside the emitted namespace where Lean prefers
  the namespace-local name. Fix: seed `unavailableIdents` from the
  enumerable set of bare names the emitter can produce.
- [ ] **S-3 — the Class-F recognizer over-approximates; `inZip` is
  dead code.** `scanRecUses` is entered as `go False elt` and every
  recursive call passes `False`, so the zip arm fires anywhere in the
  element term with no requirement that the zip be consumed by an
  `at` at the inner binder. Converts an intended emission-time named
  rejection into a check-time undischargeable obligation — violating
  the module's own reject-when-unsure discipline, which matters more
  given S-1 undermines "the obligation is the backstop". FIX-SEAM ⇒
  pause rule.

### Low / housekeeping

- [x] **RK-7 — CLOSED 2026-07-24** (75c2acfc6, C3). The axiom-audit awk output was tested for emptiness
  only, so an awk hard-error reads as a clean audit. `[V]` Confirmed
  asymmetric with the lint invocation, which checks BOTH `lint_rc`
  and output (hardened in the F1 fix). One line.
- [ ] **RK-8** — cache reuse is gated on marker EXISTENCE only;
  staged contents are never re-hashed, so anyone with write access
  to `~/.cache/saw-core-lean/lean-<fp>/` can substitute the support
  library (adding *lemmas*, invisible to the allowlist audit).
  `SAW_LEAN_ROOT` substitutes both library and checker. Defensible
  as a dev override — residual-trust should say so.
- [ ] **A-10** — the two `sorry` rules contradict each other on the
  completed path (lenient scan of `Emitted.lean` exempts the
  sanctioned `| skip); all_goals sorry));` form; the user-file scan
  is zero-tolerance; on the completed path they apply to the same
  bytes and zero-tolerance wins). Fail-CLOSED, so incompleteness not
  unsoundness: a goal carrying a sanctioned in-statement `sorry`
  cannot be discharged through the completed path unless the user
  also rewrites the tactic text. Third instance of proxy-vs-intent
  divergence; reconcile.
- [x] **A-4 — CLOSED 2026-07-25.** `prettyTerm` was the only `Term`
  case producing multi-token output while ignoring `Prec`, so a sort
  in argument position emitted `Vec 5 Type 1` (three arguments to
  `Vec`). Now parenthesised via `sortIsMultiToken`; `Prop` and
  `Type` stay bare since they are single atoms. Note the A-2 gate
  does NOT subsume this: it closes the goal route the audit named,
  but module/term emission still prints sorts at argument position.
  Loud (ill-typed artifact), never silent — fixed because it is two
  lines, not because it threatened soundness.
- [ ] **F-1** — the under-applied partial-op path emits an
  ILL-TYPED artifact and has zero compiling witnesses despite being
  marked "audited safe". Loud, not silent; the defect is the claim.
- [ ] **F-3 (contracts)** — division-wrapper error messages have no
  SAWCore backing. **F-3 (core) / LIB-4** — `saw_ctor_order`
  compares constructor names in order but not arity or FIELD order
  within a constructor, and 5 of 6 asserted datatypes are
  single-constructor, i.e. the assertion is vacuous exactly where
  the field-order hazard lives (a Cryptol record `{a : [8], b :
  [8]}` field swap typechecks while swapping every projection).
  **F-3b** — `@Eq.rec` reaches emission through a hardcoded path
  that skips `translateFTermF`, so it carries no assertion.
- [ ] **LIB-3** — `IntMod n := Int` means a BOUND `IntMod` variable
  ranges over representatives, not residues. Harmless in positive
  `∀` position; unsound only in negative position (no such emitted
  shape found). Distinct from the open F1 `n = 0` totalization.
- [ ] **F-8 / F-9** — `combineBinders` takes the lambda binder's
  annotation with the Pi's result type, translated by predicates the
  code says can disagree; a binder-NAME disagreement is loud, a
  binder-TYPE disagreement is silent. Not on the goal path, but on
  `write_lean_term`/`write_lean_cryptol_module` whose defs proofs
  import. — `SAWModule.hs:185-187` passes `InjectCodeDecl "Lean"`
  text into the emitted file verbatim with no validation or
  escaping: an unaudited text-injection seam in an otherwise
  fully-structured emitter (not reachable from user Cryptol today).
- [ ] **Documentation corrections batch**: A-3's five-plus sites
  (including the trust authority); the residual-trust sentence
  LIB-1 shows is BACKWARDS (`:496-503` says the eager carrier makes
  obligations "unprovable, not wrong" — when both sides surface the
  same message the obligation becomes trivially TRUE in Lean while
  FALSE in SAW, and the byte-exact messages chosen to stop Lean
  over-DISTINGUISHING are what let it over-EQUATE); the
  `Float`/`Double` faithfulness argument; the `divNat 2 0` ledger
  entry; `bvSExt` "stays axiomatic"; and the F-1 "audited safe"
  verdict.
- [ ] **Dead code**: `Ascription` in `prettyTerm` has only
  consumption sites — delete so it cannot be reintroduced.

### Systemic

- [ ] **A-11 — the trust kernel asks `grep` questions that only Lean
  can answer.** Six kernel rules establish properties of an
  ELABORATED Lean environment by pattern-matching over Lean SOURCE
  TEXT (goal presence, closer set, goal binding, placeholder policy,
  source lint, drift); text matching and Lean's view of the
  environment are different functions, and every place they are used
  interchangeably is a place they can disagree — they did, six
  times. Lean can answer five of the six authoritatively, and the
  checker is already positioned to ask (it compiles the user file to
  `UserProof.olean` and runs probe modules that import it): *what
  did this module declare* (subsumes the closer awk, closes A-5
  outright), *what does it depend on* (`#print axioms` over every
  added declaration — subsumes the `sorry` text scan and A-10),
  *does it prove the goal* (a real kernel-checked binding theorem),
  *did it extend the environment* (parser extensions, attributes,
  instances are enumerable — A-1/A-6/A-7 each slipped past the awk
  approximation). The honest exception: **options that change how
  the module was BUILT** (`debug.skipKernelTC`) cannot be detected
  from inside Lean afterwards, because importing a module does not
  re-check it — for that class the answer is to stop the user
  controlling the build, with the lint as a named backstop.
  Plan-of-record: `doc/2026-07-24_semantic-trust-kernel-plan.md`.

### Verification and pins owed

- [ ] Red-before/green-after regression rows for A-1, A-2, A-5 and
  S-1 under `saw-boundary/`, plus lint self-tests for A-6 and A-7
  and a `trust-tier-selftest.sh` case for the notation shape.
- [ ] A CI-harness negative row for the no-import decoy-`goal`
  vector (RK-5).
- [ ] The LIB-1 differential row (settles the highest-value
  reachability question in the report).
- [ ] Re-run the appendix witnesses as REAL rows: the audit
  exercised the shipped kernel with `lake` swapped for the pinned
  raw `lean` (every grep/awk/probe/branch is shipped code, but the
  substitution should be retired now the suite is idle).

## Release gate (continued)

- [ ] **Docs phrasing pass** (2026-07-21): rework the few remaining
  imprecise offensive-security phrasings into formal-verification
  terms (skeptical review / counterexample search /
  unsound-acceptance path / guard coverage) — the work is soundness
  review, not attack tooling, and the wording should say so.
- [ ] **Replay hardening follow-ups** (recorded at replay landing):
  CI-harness rebase onto the factored checker; binder-type
  telescope comparison in the drift check.

## 0.03 program (scheduled, user decision 2026-07-22 — do NOT start early)

- [ ] **Fragment-semantics program + recognizer extension**
  (`doc/2026-07-16_fragment-semantics-scoping.md`; its revisit
  trigger fired twice). Sequencing: Phase A pointwise-lazy lfp
  adequacy model FIRST; then the no-zip lookback-1 recognizer
  extension reviewed against that model (unlocks the s20_hash rung
  — boundary pinned at `workflows/llvm_s20hash_comp` — and the
  chacha iterate family); Phase B shape-witness reification behind
  it (recognizer becomes an untrusted compiler with Lean-checked
  output). The recognizer surface is FROZEN until then (seam-bug
  pause rule; ANY further seam bug ⇒ pause and discuss).

## Backlog — emitter and coverage

- [ ] **Lower `update` at concrete indices** (filed 2026-07-22).
  Cookbook Pattern 10 tells spec authors to avoid `update`-chain
  post-states, but arbitrary user specs will contain them; the
  current symbolic-index generate-and-dispatch emission is sound
  yet undischargeable in any harness budget (measured; the in-Lean
  architecture for the shape is preserved at commit 641533a37).
  Emit concrete-index `update` as a literal-vector rebuild or
  `Vector.set` form. Dischargeability, not soundness.
- [ ] **Constant-headed Prop domain rule + prop-former argument
  convention** (filed 2026-07-19; full design constraints in the
  archived record). Extends the kind-directed domain rule to
  constant heads and declares prop-application arguments raw.
  Unlocks 5 pinned obligation rows (IsLeNat_SuccSucc,
  bvultToIsLtNat family). Needs the full domain-map discipline
  (design doc + skeptical review — this is a `classifyDomain`
  change), and must respect the C1 standing note: IsLeNat's
  constructors/recursor do NOT structurally match `Nat.le`'s, so
  no naive mapsTo without reconciling shapes.
- [ ] **PosRep direct recursors**
  (`doc/archive/2026-07-03_direct-recursor-semantics-design.md`) —
  unlocks the recursor_nat/recursor_z/pos_values gap family.
- [ ] **natCase value-motive lowering** — un-gaps cryptol_bv_sext
  and cryptol_bv_signed_shift.
- [ ] **`Z n` / ZtoNat realization** (IntMod slate). Related open
  decision residue: polymorphic-modulus IntMod needs proof-carrying
  nonzero evidence if it ever matters (the 2026-07-23 strict gate
  rejects non-literal moduli; named in the rejection diagnostic).
- [ ] **`reverse` realization** — full rev.cry module translation;
  demo step 3 loses its `fails` wrap (step 3b already emits
  Rev.lean).
- [ ] **Zone-1 coverage census re-run**
  (`doc/2026-07-16_zone1-coverage-census.md`): its re-run trigger
  fired 2026-07-23 (IntMod gate + bvToInt fix changed the emitter
  surface).

## Backlog — examples and stretch

- [ ] **`s20_expand32` / `s20_crypt32` rungs (stretch)**: extend the
  compositional replay ladder to the full encrypt path, each rung
  over the previous rung's replay-admitted result — the complete
  salsa20 encryption verified with Lean at every link if it lands.
- [ ] **chacha20-core `core` composition re-probe (SAW-side)**: the
  earlier attempt stalled in SAW's normalizer at 80 qround override
  applications (>10 min). The 8 qround rows are now
  replay-admittable; re-probe, and if the stall reproduces, reduce
  it and file the normalizer issue upstream with the reproducer.
- [ ] **SHA512 at scale**: stretch/performance goal
  (`stretch/sha512_full_module_probe`), not a parity blocker.

## Backlog — engineering

- [ ] **Split `Term.hs`** (SWE-quality review #2; now ~5,500 lines):
  extract at least `Obligations.hs` and finish the `Convention.hs`
  split along the existing banner sections. Pure reorganization; do
  BEFORE the pre-release soundness review so the audit reviews the
  final structure.
- [ ] **lean-smt migration** (recorded resolution trigger for the
  native-eval trust tier): when lean-smt's BV proof reconstruction
  lands kernel-checked (its own BitVec tests stop admitting
  placeholders), swap `bv_decide` → `smt` on tier rows and delete
  the `.trust-tier` markers.

## On hold (user decision)

- [ ] **Upstream sync onto GaloisInc/saw-script:master** (added
  2026-07-23; ON HOLD same day: wait for the SAW maintainers to say
  how they want PR #3214 landed — merge-commit / squash / curated
  series — since two of the three outcomes would discard a sync
  done now; conflicts only block the merge button, not review).
  Facts as scoped 2026-07-23: upstream 372 commits ahead of the
  2026-05-01 merge-base (verified via the compare API); GitHub
  reports exactly FIVE conflicting files (ci.yml, CHANGES.md,
  Proof.hs, Exporter.hs, Interpreter.hs — the registration seams;
  our side there is ~30 hunks, almost purely additive, 16 deleted
  lines total); `Prelude.sawcore` has ZERO upstream commits since
  the merge-base and `Cryptol.sawcore` two; our import surface
  churn is light (SharedTerm 9 commits, the Name/Functor/
  Recognizer/Raw/QualName set 1 each). Strategy when unblocked:
  MERGE (not commit-by-commit rebase — preserves review anchors
  and per-commit tested-ness; one conflict session; ~one focused
  day incl. gates); the real risk is clean-merging behavioral
  drift, so the gate is smoketest + full suite + demo with
  hunk-reviewed golden re-pins, same bar as a toolchain bump.
  Hedge if the wait stretches: a throwaway trial merge on a
  scratch branch, never pushed, to measure resolution rot.

## Dispositioned legacy items (2026-07-24 restructure)

Open checkboxes from the pre-restructure TODO whose work had in
fact landed — dispositioned here with evidence rather than silently
dropped (full original text in the archived record):

- *Slice OP-3 (wrapped-fix contract)* — superseded by the OP-3
  successor program, R0–R4 landed 2026-07-16; wrapped
  unique-fixed-point contract retired.
- *Proof-carrying bounds/index contracts* — landed as OP-1/OP-2
  (2026-07-12); all seven sub-boxes were already checked.
- *Proof-primitive obligation contracts* — the contract path landed
  (`lowerProofPrimitiveContract`, 27 obligations rows); remaining
  families are pinned known gaps tracked by the constant-headed
  Prop and PosRep items above.
- *Bitvector primitive conformance surface* — closed to the pinned
  residue (scanl rejection; `bvLg2`/count ops realized and matrix-
  pinned 2026-07-23).
- *Comprehensive differential conformance suite* — landed
  2026-07-23 (212-case labeled edge-case matrix across ten rows,
  plus the pre-existing 100+ differential rows).
- *Audit-driven removal of legacy emission paths / delete fallback
  code / close semantics-injection paths / justify representation
  rewrites* — executed by the 2026-07-14 release audit (~110 dead
  items removed) and the 2026-07-17/18 audits; residue tracked by
  the Term.hs split item.
- *Generated-Lean readability* — ongoing style concern, no open
  work item; readability changes ride behavior changes.
- *Pin audit findings as regression tests / focused shape tests /
  soundness boundary tests / keep gates green* — standing practice
  enforced by the harness design rules, not checkbox work.
- *Refresh example/proof corpus; goldens after proof-carrying
  migration; wrapped-goal proof examples; Phase-beta simp support* —
  landed across 0.01/0.02 (corpus: 50 proofs rows, 24 workflows;
  simp support: the `_proofs` libraries + starter sets).
- *Keep recursive/fix emission on the generic proof-carrying path* —
  enforced by R4 (two-state lowering; obsolete-helper scan).
- *Decide the external proof-obligation format* — decided by
  practice: `offline_lean` emission format + `offline_lean_replay`
  admission contract (doc/2026-07-16_replay-design.md).
- *Rocq parity surface / proof-discharge workflow narratives* —
  descriptive sections, not work items; current versions live in
  STATUS.md and doc/architecture.md.

## References

- `STATUS.md` — literally-true current state + known-gap census.
- `doc/2026-07-02_position-callee-calculus.md` — the translation
  contract (canonical, maintained).
- `doc/proof-cookbook.md` — discharge patterns + the bitvector
  automation trust policy (authoritative).
- `doc/2026-07-16_replay-design.md` — replay admission contract.
- `doc/2026-07-14_release-plan.md` — 0.01/0.02 plan of record
  (historical banners inline).
- `doc/decision-log.md`, `doc/audit-history.md` — durable indexes.
- `doc/archive/2026-07-24_todo-execution-record.md` — the frozen
  buildout record (every completed item, full riders).
