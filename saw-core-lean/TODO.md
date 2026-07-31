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

## Sequencing (plan of record, 2026-07-28)

Full reasoning: `doc/2026-07-28_defect-families-and-sequencing.md`.
Every finding from both audits sorts into THREE families. Two have
named roots and written plans; the third had neither, which is why
its fixes felt like whack-a-mole — they were, because nothing stated
what would make them stop.

1. **Family 1 — the trust kernel asks TEXT questions about a
   SEMANTIC object** (A-1/A-2/A-5/A-6/A-7/R-1/A-10/RK-5/RK-7).
   Root named as A-11; plan of record
   `doc/2026-07-24_semantic-trust-kernel-plan.md`. AFTER the audit.
2. **Family 2 — no model of SAW's PARTIALITY** (LIB-1 errors, S-2
   divergence, S-1 erasability, the divNat/IntMod boundaries).
   Plan of record `doc/2026-07-16_fragment-semantics-scoping.md`;
   LIB-1's carrier remedy (a) is its value-domain instance.
   0.03, unchanged — LIB-1 ships documented under that deferral.
3. **Family 3 — EMISSION CONVENTIONS** (F-8, F-1, A-4, F-6/F-7,
   F-2 core). The open one. Proposed root: the calculus made
   *adaptation* safe (the `adaptTo` chokepoint, forbidden
   adaptations unrepresentable) but left *annotation* unguarded —
   the type a definition DECLARES is computed by a different path
   from the one that builds its BODY, over a binding vocabulary
   too coarse to carry the invariant (`BindingFunction` records
   nothing about the formals' representation, which IS F-1).
   **Missing invariant: the emitted signature must derive from the
   same authority as the emitted body.**

**Order of work, decided 2026-07-28 (user):**

- [x] **S-3 narrowing** — landed 2026-07-28 (low-risk, strictly
  narrowing; see the S-3 entry).
- [x] **THE FAMILY-3 PASS — LANDED 2026-07-29** as one pass, not
  three drive-bys. Contents as planned: the `Term.hs` split; a design
  note stating the annotation invariant and where its chokepoint
  lives (`doc/2026-07-29_annotation-invariant.md`); then the three
  open emission items folded in AS INSTANCES — F-1's top-level
  annotation, F-2 core's recursor-head qualification, and the
  unused-Pi-binder printer cosmetic. Rationale for the ordering was:
  an audit is for finding what we do NOT know, and auditing first
  spends reviewer lanes rediscovering F-1-class issues in code
  we are about to restructure; the charter's "a defect exists until
  the surface is shown sound" is also much harder to satisfy for a
  surface with no stated invariant.
  **What landed.** Split: `Calculus.hs` / `Signature.hs` /
  `Obligations.hs` extracted, layered with zero upward edges, and
  verified BEHAVIOURALLY INERT by the snapshot oracle (emitted Lean
  byte-identical across all 350 artifacts) rather than asserted.
  Invariant: *the emitted signature must derive from the same
  authority as the emitted body*, with `SAWCoreLean.Signature` as its
  named home. Instances: see the F-1, F-2 (core) and printer entries
  below.
  **What it did NOT close, for the panel to score:** the invariant is
  STATED, not enforced by construction — there is no `adaptTo`
  equivalent making a signature/body mismatch unrepresentable, and
  `mkDefinitionWith`'s second caller (`emitImportedRealizationAlias`)
  bypasses the chokepoint. Both are recorded in the design note's
  closing section.
- [ ] **Pre-release soundness review** (the panel below) — against
  the restructured, invariant-stated emitter. NOT skippable once
  the pass lands: Families 1 and 2 are deferred BY DECISION, not
  closed, and checking that those dispositions are honest — and
  that no FOURTH family exists — is exactly the panel's job.
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
## Release gate — WAVE 5 verdict (2026-07-30): gate NOT met at 237310fda — remediation in progress

Report: `doc/2026-07-30_release-gate-audit-wave5.md`. Judged
against the close-out plan's §5 exit criterion (fixed in advance).
Zero CRITICALs, zero translator/kernel defects at MEDIUM+, failure
clause did NOT fire — but clauses 1 and 2 fail on BOOKKEEPING:

- **Clause 1**: W5C-1 (MEDIUM, in-model, CONFIRMED) — CONFORMANCE.md
  advertised positive `obligation` coverage for the `*WithProof`
  contracts withdrawn as unsound 2026-07-25 (LIB-2); the
  propagation-failure class has instances in four files plus
  shipped docstrings, and doc-claim-lint is structurally blind to
  it. Remediation step 1 (documentation-propagation commit) is
  applied on this branch; the consistency agent's calibration note
  (W5C-1's MEDIUM is the outlier vs the same-class W5C-2 LOW) is
  recorded in the report, not adjudicated.
- **Clause 2**: the critic's ledger sweep found six in-model
  MEDIUM+ items with neither fix-and-pin nor user-accepted
  disposition. **DISPOSITIONS ACCEPTED BY THE USER 2026-07-31**
  ("I agree with your recommendations, go ahead with the fast
  path"), executed same day:
  1. **OBL-1 — FIXED AND PINNED.** The five stream-helper rows'
     byte-identical directive sets are differentiated: each now
     pins its OPERATION by lowered structure (not probe name),
     with a cross-matrix introduction check (every set accepts
     only its own emission — all 20 cross-pairs fail, including
     the demonstrated shift_l→shift_r mutation, which now fails
     on `absent:atWithDefaultM`/`absent:subNat`). All five rows
     green through the real harness.
  2. **W2-UNRUN-2 — re-score DONE 2026-07-31, and it found a LIVE
     in-model CRITICAL behind the filed item. THE RELEASE WAS
     BLOCKED; the defect is now FIXED AND PINNED.** The filed
     `FpOther` blindness is only LOW coverage debt (0.03 carry,
     pin sketch at its entry). The live defect was gate 3's TEST 1
     exempting every NAMED binder: `(h : EqTrue …) -> …` via
     `parse_core`/`prove_core` emitted while the identical
     anonymous goal was refused. Verified independently end-to-end
     at the pre-fix HEAD: SAW proves the hypothesis and refutes
     the conclusion (obligation FALSE), the emitted goal proves in
     Lean with `[propext, Quot.sound]` — both ALLOWLISTED — so
     replay would have issued evidence for a false claim. FIX: the
     gate now runs the printer's own `anonymizeUnusedPiBinders`
     before TEST 1's anonymity question, so it inspects the
     binders the artifact ships (proceed → reject; C7-safe
     direction). PIN: `saw-boundary/goal_except_carried_binder_refusal/`
     `except_carried_named_hypothesis`, with the stated mutation.
     Over-refusal checked: named-dependent and named-unused VALUE
     binders still emit. Root-cause analysis (the §5 failure
     clause deliverable): `doc/2026-07-31_why-gate3-escaped.md`;
     new rule C8 governs limit-narrowing.
  3. **F11** — USER-ACCEPTED explicit 0.03 carry (architecture.md
     module-map completeness; doc-only).
  4. **LIB-W2-3** — USER-ACCEPTED explicit 0.03 carry, with the
     recorded risk note: LOUD today only by accident of `Rat`
     division not kernel-reducing; the loudness pin is the 0.03
     item, and a toolchain that makes `Rat` reduce removes the
     accident with nothing watching.
  5. **F8b — CLOSED AS UNCONSTRUCTIBLE** (the F-9 treatment; the
     triggering script cannot be written because the emitter
     refuses the shape upstream).
  6. **F12 successor** — USER-ACCEPTED explicit 0.03 carry (joins
     the lint-token collapse and the doc-claim-lint mechanism in
     the 0.03 harness rework).
- **Clause 3**: green by inheritance at 237310fda; per-commit —
  re-sweep owed at the post-remediation release commit.
- **Clause 4**: pending merge/CI (user decision).

Wave-5 residue dispositions are folded into the wave-4 section's
STILL OPEN list below (14 dispositions, 3 closures, 2 sharpenings);
the delta lane found the seventeen-commit composition SOUND (33
tokens exactly pinned-or-waived, gate order re-derived); filed for
0.03, mechanism-shaped: declaration-existence resolution for
doc-claim-lint (the propagation class becomes a check).

## Release gate — WAVE 4 findings (2026-07-30): no blocker, two docket items NOT closed

Report: `doc/2026-07-30_release-gate-audit-wave4.md`. Five Opus
docket lanes at HEAD `b5c75fd09`, per-finding adversarial verify,
plus the two commissioned harness improvements: the cross-finding
CONSISTENCY agent (ran; found and resolved 4 contradictions, two of
which would have put false coverage claims in this ledger) and
severity scored against the citable threat model (first wave). 29
raw findings → after verification 2 MEDIUM, 27 LOW/INFO, 0 CRITICAL.

**Verdict: nothing release-blocking under the threat model. Docket
items 3 (cabal ship-list) and 4 (consistency check) closed; items 1
(FixRecognizer) and 2 (demo) NOT closed — item 2 escalated.**

### WAVE 5 CHARGES (open)

- [x] **W5-1: reject-side H_prod pin (GAP 1) — LANDED 2026-07-30,
  witnesses corrected same day by its fix audit.**
  `support-lemmas/fix_hprod_refutation/proof.lean`: kernel-checked
  POSITIVE refutations (stronger than the charged `.shouldfail`
  form — undischargeability is a theorem, not one tactic's
  failure). The FIRST cut was refuted by the opus fix audit on two
  MEDIUMs: its witnesses all fired at index 0, which every
  recognizer-admissible body pins to a rec-free seed
  (`FixRecognizer.hs:240/:245/:134-152`), so they sat OUTSIDE the
  mutated recognizer's image and pinned only "H_prod is not
  vacuously true"; and one companion had beta-reduced into V-H1
  vacuity. Corrected form: named witness `def`s (no beta-reduction
  possible), all seed-guarded at index 0 and refuted at index 1 —
  Class F at `n = 2` with `w[1] = v[1]` (the semantics of
  `at rec (addNat i2 1)`, the read the `:350` guard refuses — the
  first cut's docstring had the guard's polarity inverted, also
  audit-caught); stream self-reference (kills stream `lookback`,
  `faithful` holds) and iterate-transform (kills `faithful`,
  `lookback` holds, companion stated with the witness applied).
  Row green via `lean-proof-test.sh` (elaborates + axiom audit).
  **FXC-1/FXC-2's LOW is no longer provisional.** Residue accepted
  from the audit (its F4, INFO): companions are hand-stated field
  shapes, so they track the witnesses but not field-shape drift;
  only the `¬` theorems (which project `h.lookback`/`h.faithful`)
  alarm on drift, and they are the load-bearing half.
- [ ] **W5-2: the demo's CI gate cannot have been green since
  2026-07-18 (GAP 2 — verified at HEAD).** `ci.yml:817-833` runs
  `saw demo.saw` with no `SAW_LEAN_ROOT` anywhere in `.github/`, on
  a `dist/bin/saw` extracted from dist-newstyle with a baked
  never-installed `~/.cabal/share` datadir; `demo.saw:66,69` call
  `offline_lean_replay` (two branches only, `Builtins.hs:1461-1479`;
  abort reproduced locally with same provenance); the leg is real
  with `continue-on-error: [false]`. **Exactly one of: the
  `saw-core-lean-tests` leg is red at HEAD, or that leg is not
  running.** Undeterminable offline; determine which, then fix (one
  `export` in ci.yml, or ship data-files in `bundle_files` — the
  latter also remedies SHIP-1). The demo's
  `proof/replay/{invol,eq}/proof.lean` are user-authored proof-side
  files gated ONLY at demo time — ungated for twelve days.
  **REMEDY LANDED 2026-07-30 (both halves): ci.yml demo step now
  exports `SAW_LEAN_ROOT="$PWD"`; `bundle_files` ships
  `saw-core-lean/{lean,replay}` into dist via `git archive`
  (derived, not a hand list — tracked files only, no `.lake`),
  which makes the unpacked dist root a valid `SAW_LEAN_ROOT` and
  resolves the bundled demo lakefile's `../../../saw-core-lean/lean`
  require. This also discharges SHIP-1's mechanism. STILL OPEN, the
  determination half: whether the `saw-core-lean-tests` CI leg was
  red or not running for the 07-18..07-30 window — needs network
  access to CI history; record the answer here when available.
  Narrowed by the fix audit (F4): the leg's matrix entry, os, and
  `continue-on-error: false` are all live in-repo, so "not
  running" is possible only if the workflow never ran on this
  branch at all — in-repo config cannot explain a silently-skipped
  leg. Note the fixed step is verifiable only by CI itself (this
  sandbox cannot run GH Actions).**
- [ ] **W5-3: cross-check `CONFORMANCE.md:60`'s pin inventory (GAP
  3).** The coverage lane surveyed ~half of it; its "nothing lets an
  unsound shape through at HEAD" is a partial-survey result.
  Specifically re-establish or reclassify
  `differential/fix_error_elem`: a SAW-vs-Lean agreement claim for
  an error-carrying element in a recognized Class-F fix, sole
  evidence a one-time manual `#reduce` from 2026-07-16, four backend
  deltas since. In-model, never scored by any wave.
  **PARTIAL 2026-07-30: the fix_error_elem half is DONE** — the
  `#reduce` observation re-established mechanically at HEAD on the
  currently-emitted artifact (bytes decode to the identical
  message; procedure recorded in the row's KNOWN GAP comment), and
  all nine skipped inventory rows confirmed present and riding the
  green suite. STILL OPEN: the semantic re-read of those rows
  (does each pin what the table says it pins) — wave-5 lane work,
  not a mechanical check.

### Surviving MEDIUMs (non-blocking)

- [x] **SHIP-4 (MEDIUM, the wave's only CONFIRMED verdict) — FIXED
  2026-07-30.** XDG cache staging race: `staging-tmp-<fpTag>` was
  shared by concurrent same-fingerprint processes (no
  pid/lock/O_EXCL); verifier found a marker-plus-hole interleaving
  the lane missed — P1 writes `.staged-ok` into P2's recreated
  tree, renames a tree missing the head of `relFiles`, and the
  marker short-circuit makes the broken cache PERMANENT. Fix: the
  staging tmp dir is per-call-unique (`createTempDirectory`,
  matching the per-call stage dir and the kernel's `WORK` dir) and
  the shared-name leftover delete is gone — both the
  delete-a-live-peer race and the marker-plus-hole publish are
  structurally impossible. Tradeoff (crash debris under the cache
  base; never trust state — markerless trees are never consulted)
  recorded at the site. NOTE: the branch remains suite-unexercised
  (SHIP-2); the fix is argued structurally, not pinned.
- [x] **SHIP-1 (MEDIUM, was HIGH) — MECHANISM FIXED 2026-07-30
  (with the W5-2 remedy).** Original filing: the release bindist
  never contained the data-files (`bundle_files` copied nothing
  from `saw-core-lean/`; no `cabal install`/`sdist` in
  `.github/`); `offline_lean_replay` unusable in the tarball while
  `Interpreter.hs:5333` and `STATUS.md:359` claimed otherwise.
  Now: `bundle_files` ships `saw-core-lean/{lean,replay}` (derived
  via `git archive`), the abort message names the unpacked-tarball
  root as a valid `SAW_LEAN_ROOT`, STATUS.md carries the bindist
  caveat, and the demo README documents the tarball flow.
  Residues from the W5-2 fix audit, accepted at LOW/INFO
  (annotated 2026-07-30 evening after the close-out step-1 audit
  caught two of these gone stale): the tarball tree must be
  writable (read-only prefixes fail closed; `saw_datadir=<dist
  root>` is the read-only-capable alternative — recorded in the
  ci.sh comment); ~~the demo-pin divergence~~ RETIRED — pins
  converged 2026-07-30, the tarball ships both projects at
  v4.32.0; ~~the 120s-cap concern~~ MEASURED AND RETIRED
  2026-07-30 (step-1 audit F4 reconciliation): a from-scratch lake
  build of the staged library is ~3.2s and the whole cold
  data-mode leg ~7.5s — getting-started's "a few minutes" was the
  elan toolchain-DOWNLOAD case, now stated as such; the one
  unmeasured sliver is that download riding inside the kernel's
  120s cap on a fresh machine (network-bound, unmeasurable from
  this sandbox — CI installs elan before any replay runs, so CI is
  not exposed); help text at `Interpreter.hs:5333`
  still says "installed data-files" (true under cabal install,
  wrong for the bindist) — OWN LINE now, no longer carried by the
  closed pin-convergence item: fix with the next Haskell batch.

### LOW/INFO residue (fix-shortlist in report §6) — dispositions 2026-07-30

LANDED same day (each with an opus fix-audit; see the commits of
2026-07-30 after the wave-4 report):
- FXC-1: `:350` guard now pinned by a SmokeTest exact-reason case
  (deleting the guard goes red), and its H_prod discrimination is
  kernel-checked (W5-1 row). FXC-2's stream-side H_prod likewise;
  the `isIdentityStreamRead` unit pin (needs `Stream#rec` term
  construction in SmokeTest) remains OPEN below.
- FXC-3: the `:280-287` spec comment rewritten to the implemented
  rules, fossil provenance named.
- DEMO-1..6: README/demo.saw truthfulness batch (SAW_LEAN_ROOT in
  the command blocks + tarball flow; clobber warning; Rev.lean
  header contradiction; trust-story link + retired idiom dropped;
  require path; Files section). DEMO-7 partially (phantom
  proof/README reference removed from ci.yml; the unpinned
  duplicate copies remain OPEN below).
- DC-1..5: prose narrowings, the token split (`axiom-decl-in-user-file`
  vs new `proof-source-unlintable`, axiom-first precedence),
  END-block + fatal-half pins, denominator correction.
- SHIP-1/SHIP-4: see their entries above.

STILL OPEN — re-sworn by wave 5's residue-adjudication lane
(2026-07-30 evening; each carries a wave-5 disposition, all 0.03
carries unless marked; the list previously understated progress in
four places — FXC-6, SHIP-2, SHIP-3 landed in close-out step 1, and
DEMO-8 closed — caught by the wave-5 critic, gap 4):
- FXC-2 unit pin for `isIdentityStreamRead` — DEMOTED to INFO,
  defer to 0.03 (R5-RES-1: protects only which diagnostic an
  unrealizable stream fix is refused with; the false-positive
  image is kernel-refuted by `fix_hprod_refutation` and the
  dispatch fails closed twice over).
- FXC-4 INFO (digit leak latent by margin AND reachability,
  R5-RES-2); FXC-5 INFO (the precise diagnostic is parse_core-only
  defense-in-depth, R5-RES-3).
- ~~FXC-6~~ FIXED in close-out step 1 (`183bfd6c0`). FXC-7 INFO
  (dead by pattern order, R5-RES-4); FXC-8/FXS-2 INFO (the
  blind-spot note is still smaller than the truth — zip's four
  slots, R5-RES-6); FXS-1 INFO KEPT OPEN — the module header still
  does not record the `VarIndex` uniqueness assumption (R5-RES-5).
- DEMO-7 LOW, SHARPENED by wave 5 (R5-RES-7): the drift does NOT
  fail closed — each copy is checked against its own goal copy, so
  a stale demo obligation stays green. 0.03 carry.
  ~~DEMO-8~~ CLOSED (R5-RES-8: the bindist ships the demo in the
  layout its `require` needs; the surviving gap is sdist-only and
  no release path runs sdist).
- ~~SHIP-2~~ / ~~SHIP-3~~ LANDED in close-out step 1
  (data-mode-selftest with cold+warm legs; ship-list-check).
  SHIP-5 INFO (unguarded reads, fail-closed, no supported
  installer produces the partial install, R5-RES-9). ~~SHIP-6~~
  CLOSED as already-catalogued (verbatim in residual-trust §3.2c,
  R5-RES-10).
- From this arc's own audits (wave-5 adjudicated): ~~triviality
  denylist future-phrasing sliver + no-live-row (R5-RES-11)~~
  DISSOLVED 2026-07-31 — the gate was deleted (design review
  Option B, user decision); `:(glob)` red-direction row INFO
  (semantics now observed, value bounded by the no-subdir
  precondition, R5-RES-12); elan-download-inside-120s-cap LOW
  (R5-RES-13: real for a first-run bindist user, not CI);
  ~~trivgoal_deep harm story (R5-RES-14)~~ moot with the gate.
- Wave-5 delta-lane LOW/INFO, 0.03 carries: DC5-2 (deleted
  `Generated.lean` rejects under the caller-contract token, not
  the deletion token — fail-closed, wrong name); DC5-3
  (census/oracle "shared definition" is two different walks with
  the same domain today); DC5-4 (`replay-kernel-selftest.sh clean`
  can never remove anything — `$$` of the cleaning shell); DC5-5
  (ship-list sub-check (c) prints no verdict after an earlier
  failure); DC5-1 folded into the CP-3 entry above.

### Consistency-agent corrections (harness improvement: LANDED, worked)

Two verifier claims must NOT enter this ledger as coverage: "a
marker-bearing cache dir is necessarily complete" (refuted by
SHIP-4's interleaving) and "every harness runs lake build before
lake env lean" (all five sites sit inside `SAW_LEAN_SUITE_LAKE_PREBUILT`
skips; one build per sweep — which is why the 2026-07-29 16-row
incident happened the day AFTER the prebuild hoist). Scoring seam
found: `in_model` was scored under two mutually exclusive rules
(9 findings vs 4); resolution — the operative test is consequence 1
(`residual-trust.md:64-69`): does the defect require an adversarial
author? Doc-only defects are in-model. One sentence at `:62` closes
the seam.

## Release gate — WAVE 3 findings (2026-07-30): verdict since re-scored

*(Original verdict at filing: STILL DO NOT RELEASE. Re-scored the
same day under the D1 threat model: the surviving in-model blocker,
W2-UNRUN-1, is FIXED; K-1/CP-1/K-3 close out-of-model; K-2 drops to
LOW. Agreed release posture: ship with the trust kernel declared
WIP and health warnings to beta users, once the D2/D3 hardening —
tasks #26, #27, #20 — lands. STATUS 2026-07-30 end of day: ALL
LANDED (commits c0862d5c5, 6c3557cdc, 0c9451449), each followed by
a focused opus fix-audit whose surviving findings were closed in
0c9451449; full cabal-path suite GREEN at 0c9451449 (1361s, 72
known gaps as pinned) plus smoketest PASS. The release precondition
this note names is met.)*

Report: `doc/2026-07-30_release-gate-audit-wave3.md` (five docket
lanes + five fresh Opus lanes, refute-by-default, second lens on
surviving CRITICAL/HIGH, a skeptic per docket verdict, completeness
critic. 87 agents, HEAD fd1201f9d.) 24 findings survived, 19 refuted.

**THE SCORECARD: the convergence proposal's §5 prediction is
REFUTED** — K-2 is a CRITICAL in a chokepoint, W2-UNRUN-1 is a second
CRITICAL in a chokepoint, and even the confirming CRITICAL (K-1) is
outside §4's six enumerations. The mechanism half survives (hand
lists rot, and dominate by volume); the single-cause frame does not.
This wave's CRITICALs cluster in the trust kernel's ORDERING and
EXISTENCE assumptions. See the report §1.

### >>> SUPERSEDED IN PART BY THE 2026-07-30 DOWN-SCOPE DECISION <<<

Read this before acting on any kernel entry below. Four decisions were
taken after wave 3 reported, and several entries below are now wrong
about what should be done.

**D1. THREAT MODEL: the replay trust kernel defends against USER
ERROR, not adversarial proof authors.** Previously unstated, which is
why kernel guards were designed against an attacker and kept losing.
LANDED 2026-07-30 (task #25): the citable statement is
`doc/2026-05-02_residual-trust.md` §Threat model, with the wave-3
kernel findings re-scored under it in a table there; user-facing
consequence in README; reviewer-facing scope rule in
contributing.md ahead of C1–C4; D1–D4 recorded verbatim in
`doc/decision-log.md`.

**D2. The proof-side lint narrows (plan 3a). EXECUTED 2026-07-30
(task #26).** `proof-source-lint.awk` goes from a 22-command denylist
+ 221-line lexer to ONE closed check: no `axiom` declaration. That is
all the `native-eval` tier's single pattern rule needs protecting
from; the strict tier is exact-match on five fully-qualified names
and needs no lint at all. As executed, the F1-hardened lexer machine
was kept VERBATIM (every post-F1 defect in the file was in the rules,
never the lexer — rewriting a stable audited machine smaller is the
churn this pivot stopped), so the file is ~186 lines rather than the
estimated ~30; the RULES went from 22+3 to 1. Fail token renamed
`axiom-or-macro-decl-in-user-file` -> `axiom-decl-in-user-file` (C2:
the old name claimed macro coverage). Cost measured at zero: 0
legitimate proof-side files flagged. (Denominator corrected by
wave-4 DC-5: "103" was not reproducible; the 2026-07-30 re-sweep
over every tracked proof.lean/completed.lean flags exactly the 3
deliberate saw-boundary rejection fixtures and nothing else. The
zero-cost property itself was verified true.) Retired with their subjects:
`replay_reject_notation` (row), 17 trust-tier lint_case rows, A-6's
gsub. Plan 3b (retire `native-eval`, cost: 14 rows whose own comments
already plan the `bv_decide` -> `smt` migration) is HELD IN RESERVE if
defect-free proves unreachable.

**D3. `completed-outline-drift` STAYS**, hardened. **EXECUTED
2026-07-30 (task #27).** Its mechanism is sound — it asks Lean via a
fixed-literal `rfl` probe, and the R-1 awk hole was removed in July.
Its one weakness was that it used `#check`, the idiom A-5 defeated
and `contributing.md` rule 5 forbids. As executed: THREE sites, not
one — the kernel probe is now `theorem __drift_binding`, and the
suite harness's two sibling probes (fixed-literal + R3b per-def)
became anonymous `example` declarations, with the harness's F2
vacuity guard flipped to match in the same commit.

**D4. Obviated fixes are thrown out, not parked.**
- **K-1 (below): NOT A BLOCKER. Obviated by D2** — the allowlist
  inversion is unnecessary once the denylist shrinks to `axiom`, and
  `simproc` forgery requires deliberate action, which D1 puts out of
  model. The 7-head corpus measurement taken for it survives as the
  rationale for D2.
- **CP-1 (below): NOT A BLOCKER.** Pure anti-mutation-mid-check.
- **K-2 (below): down-scoped to ~3 lines**, LOW not CRITICAL. Keep
  only that `verify_unchanged` must FAIL when a staged file has
  vanished — wrong under any threat model, per rule C3 — and drop the
  path-latching half.

**Also corrected: the wave-3 `bitvector` claim is WRONG.** The report
(§1) cites `bitvector` as an unswept sixth member of the type-collapse
class, vindicating the convergence proposal's §6 hedge. It is not a
member: SAWCore has **no `bitvector` declaration at all** (the name
occurs only in comments; instrument controlled against `Vec` and
`IntMod`, which are found as `primitive`), it appears in **zero**
emitted corpus artifacts, and the support-library `abbrev` is
referenced nowhere outside its own file. **Do NOT seal it** — that
would change the support library for no soundness gain. The class
stands at FIVE members, closed. This does not rescue §5's prediction,
which remains REFUTED on its other three counts; only §6's
"I found a sixth" vindication is withdrawn. What IS real here is LOW:
`Bit` and `bitvector` are dead treatment keys whose comment asserts
routing that cannot occur — same family as F-W3-HE-3. The right fix is
the mechanism (a derived check that every
`sawCorePreludeSpecialTreatmentMap` key resolves to a real SAWCore
declaration, extending `auditLeanOpaqueDeadEntries`), not deleting two
entries.

### BLOCKS RELEASE

- [x] **K-1 — CLOSED OUT-OF-MODEL (D1/D4, 2026-07-30), fix
  discarded.** Original filing (CRITICAL, hand-enum):
  `replay/proof-source-lint.awk:208-211` bans 22 command heads;
  `simproc`/`dsimproc`/`builtin_simproc` are not among them
  (verified: zero occurrences in the file), and the word-boundary
  class includes `_` so every `*_elab`-suffixed command escapes too.
  Gives a proof-side file elaboration-time IO plus unchecked
  `addDecl`. Re-scored under the threat model
  (`residual-trust.md` §Threat model): forging a `simproc` is
  deliberate circumvention, out of model. The allowlist inversion is
  discarded; the lint instead NARROWS per D2 (task #26), and the
  finding's real lesson (a denylist of Lean commands cannot be kept
  complete) is recorded as D2's rationale.
- [x] **K-2 / CP-2 — DOWN-SCOPED to LOW (D4, 2026-07-30); in-model
  residue LANDED same day (task #20).** Original filing (CRITICAL,
  chokepoint): `verify_unchanged` (`lean-check-core.sh:132`) returns
  SUCCESS for a file that no longer exists, and completed-vs-plain
  is re-derived from filesystem state at eight `[ -f … ]` sites.
  Under the threat model, mid-check deletion as an ATTACK is out of
  model; a staged file VANISHING is an in-model tool failure that
  must fail closed (rule C3). KEPT: `verify_unchanged` now fails
  `user-file-deleted-mid-check` on staged-then-vanished, pinned by
  kernel-selftest case `b1del` (red-before verified by mutation:
  restoring the fail-open head turns b1del red). DROPPED:
  path-latching — the vanished file is caught at the next
  verify_unchanged naming it on either path, so latching is not
  needed for the residue.
- [x] **W2-UNRUN-1 (CRITICAL, chokepoint) — FIXED 2026-07-30,
  mutation-verified, then fix-audited and corrected twice.**
  My wave-2 non-reproduction was a single-test-case artifact: the
  telescope pin's ARITY half fires only when the OUTERMOST BINDER'S
  DOMAIN has a repeated subterm (P-1 share detection does not descend
  into Pi bodies), which hoists the `let` and collapses the emitted
  arity to 0. Without that repeat the arrow survives and the goal
  emits with an Except-carried, uninhabited binder domain while SAW
  proves the same hypothesis TRUE — reachable from ordinary Cryptol,
  and it bit EMISSION-ONLY users, who never touch replay.
  FIX AS LANDED — deliberately broader than this ledger's own
  prescription, which said "gate in `writeLeanProp` only": goal-shape
  GATE 3 (`leanExceptCarriedGoalBinders`) inside
  `SAWCoreLean.Term.translateDocWithTelescope`, so it applies to the
  goal path itself rather than one call site. `write_lean_term` is
  unaffected because it is `DefEmission`, so the
  `obligations/proof_bv_eq_to_eq` row that legitimately carries the
  shape still emits (verified).
  PINNED by `saw-boundary/goal_except_carried_binder_refusal`
  (error-free + erring probes). Mutation: neutralize the gate and both
  probes emit the vacuous goal.
  THE FIX AUDIT FOUND FOUR DEFECTS IN MY FIX, all corrected:
  (a) HIGH over-refusal — it refused a function-typed goal binder,
  whose value image legitimately wraps to
  `Except String Bool -> Except String Bool` and is STRONGER than the
  SAWCore type, not weaker; and it handed that user the hypothesis
  diagnosis, blaming a `goal_cut` they never wrote — the very defect
  the guidance refactor existed to prevent. Gate 3 now exempts value
  images (final codomain carrier-headed). I had already seen this
  shape in my own smoketest and explained it away.
  (b) the spine walk stopped at the first non-Pi, so a hoisted `let`
  DISARMED gate 3 entirely; coverage of that class was accidental
  (the arity half). It now descends through `Let`, as
  `leanSortBinders` always did.
  (c) my `Exporter.hs` claim that gate 3 "covers every caller" was
  false in both directions; the two halves are complementary and the
  arity half's placement at the call site is positional safety.
  (d) a dead guard, an over-precise mechanism claim, an overstated
  row header, and a comment/code mismatch — all corrected.
  KNOWN LIMIT, recorded not overclaimed: the gate tests for the
  CARRIER, not for uninhabitedness. A raw uninhabited hypothesis
  domain (`@Eq Bool Bool.false Bool.true`) still emits; that is
  faithful rather than weaker, but it rests on "raw implies faithful",
  which is an argument and not a check.
  **The README LIB-1 hold is now discharged**, at MEDIUM
  incompleteness rather than the falsity wave 2 claimed.
- [x] **CP-1 — CLOSED OUT-OF-MODEL (D1/D4, 2026-07-30), fix
  discarded.** Original filing (HIGH, chokepoint): last
  `verify_unchanged proof.lean` is `:351`; the `UserProof.lean`
  copies are `:418` and `:452`; the audited artifact and closer list
  are built from bytes no text gate saw. The agent that could
  rewrite those bytes between gate and copy is an authored
  metaprogram — pure anti-mutation-mid-check, out of model.
- [x] **K-3 — REINSTATED by the critic, then CLOSED OUT-OF-MODEL
  (D1, 2026-07-30).** The reinstatement stands as a matter of
  record: its refutation rested on "no elaboration-time IO route
  survives GATE B" while K-1 confirmed such a route, and the
  harness's inability to hold both was a real audit defect (see
  WAVE 4 SCOPE, consistency check). But the route itself is
  deliberate circumvention — same disposition as K-1. K-7
  scenario 2 likewise.

### SHOULD FIX BEFORE RELEASE

- [x] **W3-REF-1 — re-scored 2026-07-30 (close-out arc step 2):
  HIGH → LOW; mechanism fix LANDED same day in `aa7c06f24`** (the
  ledger briefly said "queued" after the fix had landed — caught by
  that commit's own audit, F3; the entry text below is the
  re-score's record, its "fix to land" now reads "fix as landed"). The count is
  confirmed at HEAD: the extractor (`SmokeTest.hs` `marker =
  "Lean.Ident \""`) cannot see the tactic STRING built at
  `Contracts.hs` `checkedEvidenceScript`, and exactly nine of its
  bare citations are in neither `emitterBareNames` nor
  `hardcodedBareNames` (`natPos_macro`, `bit0_macro`, `bit1_macro`,
  `one_macro`, `zero_macro`, `divNat_eq_div`, `modNat_eq_mod`,
  `divNat_checked_eq_div`, `modNat_checked_eq_mod` — the macro five
  registered only in their qualified spelling, the four bridge
  lemmas nowhere). But all nine live inside a `by` script only —
  the obligation STATEMENT is emitted fully qualified — so a
  capture cannot change what an artifact means: user defs give
  definitionally-true equations (still a kernel-checked term), or
  the script falls to `all_goals sorry`, which the zero-tolerance
  sorry scan and the `sorryAx`-rejecting axiom audit refuse loudly.
  In-model, sound-or-loud, LOW. Fix to land (the re-score's
  recommendation, ~10 lines, verified churn-free — no .cry/.sawcore
  defines any of the nine): give `checkedEvidenceScript` a
  `[Lean.Ident]` simp list, render the tactic from it, export it
  into `contractEmittedNames` — registration by construction; and
  narrow the over-claiming lint comment at
  `SpecialTreatment.hs:477-481` to "inline `Lean.Ident` literals".
- [x] **W3-HR-4 / W3-REF-3 (HIGH/MEDIUM, derived-enum) — RE-SCORED
  AND CLOSED-BY-PIN 2026-07-30 (close-out arc step 2).**
  `supportLibraryFiles` walk is non-recursive (verified) and the
  agreement test reads only the root's imports. Latent today, which
  is how the previous five rotted. Under the threat model the
  latent trigger is one event — a subdirectory appearing under
  `CryptolToLean/` — and that event now fails the suite loudly
  BEFORE any non-recursive walk can silently miss:
  `support/ship-list-check.sh` pins "no subdirectories" as a hard
  check (it is also the cabal glob's and `relFiles`' shared
  precondition). The walks stay non-recursive by design; the design
  assumption is now checked instead of assumed. No longer
  release-relevant; revisit only if the library ever wants
  subdirectories, at which point every non-recursive consumer must
  change together (the check's failure message is the list).
- [x] **`bitvector` unswept-member claim — WITHDRAWN (refuted
  2026-07-30**, `doc/2026-07-30_bitvector-claim-refuted.md`; details
  in the supersession block above). SAWCore has no `bitvector`
  declaration; the class stands at five, closed; my "exactly five"
  claim was RIGHT and proposal §6's hedge is withdrawn. Residue is
  LOW and mechanism-shaped: derive a check that every
  `sawCorePreludeSpecialTreatmentMap` key resolves to a real SAWCore
  declaration (extends `auditLeanOpaqueDeadEntries`), which retires
  the dead `Bit`/`bitvector` keys as a side effect.
- [x] **Anti-trivialization gate is fail-OPEN (CP-3 + K-5) —
  RE-SCORED in-model MEDIUM AND FIXED 2026-07-30 (close-out arc
  step 2).** Any non-zero probe exit read as "not trivial" — tool
  failure failing OPEN inside the trust kernel (a lean crash,
  timeout, or import failure silently waved a possibly-trivialized
  goal through), against rule C3; the one pre-threat-model item
  whose shape was acceptance-adjacent. Fix: the only accepted probe
  failure is the tactic failing INSIDE the probe (Lean reports it
  at `triviality-probe.lean:2`); anything else fails closed under
  `triviality-probe-inconclusive`. Hand-mutation verified (simulated
  empty-transcript timeout on the honest control stage yields the
  token). SUPERSESSIONS (recorded per wave-5 DC5-1 — this entry
  originally described only the FIRST of what became three fixes):
  the same-day fix audits then (2) replaced the position-only
  check with a refutation-shape ALLOWLIST after demonstrating a
  resource give-up at the probe's own line admitted an
  rfl-closable goal, adding the live `trivgoal_deep` pin and
  DELETING the env-class waiver this entry cited (redundancy
  rule); and (3) paired the allowlist with a give-up DENYLIST
  after the launder channel (SynthInstance rethrow;
  nested-error formatting) was proven from Lean's source —
  denylist evidence is a hand-mutation (no live row; R5-RES-11).
  Final state as of the close-out arc: accept = allowlist AND NOT
  denylist; kernel selftest ALL CASES OK.
  **FINAL SUPERSESSION 2026-07-31: the GATE ITSELF WAS DELETED**
  (user decision, kernel design review
  `doc/2026-07-31_kernel-design-review.md` §3.1 Option B — three
  decoder rounds in one day were the empirical proof the check
  could not be kept small-and-honest). The fail-open defect this
  entry closed cannot recur because the mechanism no longer
  exists; the class it guarded is now the DOCUMENTED residual at
  residual-trust.md §3.2f, and contributing.md rule C7 governs any
  re-entry. trivgoal/trivgoal_deep retired with it; the denylist
  no-live-row item (R5-RES-11) and the future-phrasing sliver
  dissolve.
- [ ] **Gate-path divergences (13 confirmed) — RE-SCORED 2026-07-30
  (close-out arc step 2): in-model tool-failure class, one
  divergence FIXED, remainder dispositioned-not-refactored.** The
  cabal path REPLACES the environment; `SAW_LEAN_FAIL_ON_KNOWN_GAPS`
  was dropped on that path only — FIXED (added to Test.hs's
  passthrough with a comment recording why `SAW_LEAN_ROOT` stays
  deliberately absent). The remaining divergences (the paths can
  test DIFFERENT saw binaries; strictest verb unwired; the CI third
  path) are real but their failure direction is spurious
  divergence/confusion between HARNESS paths, never an unsound
  acceptance — and the memory-recorded discipline (name which path
  a green claim came from) plus the W5-2 CI fix cover the observed
  incidents. "One mechanism should own env construction" is a
  refactor, not a small-and-obviously-stable fix; it fails the
  pivot's churn test and moves below the line to 0.03. Not
  release-blocking under consequence 1.
- [x] **LIB-W2-2 residue — re-scored 2026-07-30 (close-out arc
  step 2): MEDIUM-HIGH → LOW, comment fixed; the line reference was
  wrong twice over.** The cited range drifted across a function
  boundary: `proofObligationPlaceholder`'s comment IS kept (the
  zero-tolerance sorry scan plus the `sorryAx`-rejecting axiom
  audit — two independent gates), while the guarantee wave 2
  actually cited is `unsafeAssertProofScript`'s docstring, which
  was still stated unconditionally on the Haskell side after its
  Lean twin gained the "PRECISION (LIB-W2-2)" injectivity paragraph
  (`SAWCorePrimitives.lean:1634-1655`) — asymmetry now closed by
  mirroring that paragraph into the docstring. "Three latent
  unswept members" was stale: Float/Double and IntMod are sealed
  (IntMod in `aff7fadb7`, pinned by `negative/intmod_type_collapse/*`),
  `bitvector` withdrawn — leaving TWO: `Integer := Int` (latent, no
  surviving SAW-distinct sibling, `integer.shouldfail` pin) and
  `Rational := Rat` (live value-level collapse, LOUD only because
  `Rat` division does not kernel-reduce — tracked under its own id
  LIB-W2-3 MEDIUM with its loudness pin owed there, not here).

### CORRECTIONS TO THIS LEDGER (made by wave 3)

- [x] **OBL-2 DOES NOT EXIST — phantom finding, removed.** `grep OBL-2`
  returned exactly one hit whose body was OBL-1's content. The wave-2
  report's finding list contains OBL-1/OBL-4/OBL-6 only. **OBL-1 is
  MEDIUM, not HIGH** (five byte-identical `expected.txt`, md5
  `a494642d…`; only three of six directives are live). A wave-3 lane
  re-asserted it as "confirmed and stronger than filed" and its
  skeptic caught that.
- [x] **W2-UNRUN-2 CONFIRMED-DEBT** — the FpOther blindness is real
  and is half of W2-UNRUN-1's mechanism.
- [x] **Unapplied `coerce`: NOT UNSOUND** — unsound-SHAPED but loud
  by construction. Disposition: accept-documented, plus one narrow
  Phase-β follow-up. Closes the item logged 2026-07-29.

### WAVE 4 SCOPE — RAN 2026-07-30 (report: `doc/2026-07-30_release-gate-audit-wave4.md`)

- [ ] **`FixRecognizer.hs` (461 lines) — read by NO wave-3 lane.**
  `classifyFixShape` is a hand-written syntactic classifier whose own
  comment (`:280-287`) says a same-index or computed-index body must
  not classify because "it would be unsound to lower"; consumed at
  `Term.hs:1303-1312` to choose lowering vs refusal. A CRITICAL-class
  admissibility gate implemented as a hand enumeration, never audited.
  **Wave 4's first charge.**
  **AUDITED 2026-07-30, NOT CLOSED**: strong on the Haskell side (no
  unsound classification constructed; fail-closed dispatch;
  Left-dominant veto; derived recursive walk), but the severity
  architecture rests on the unmechanized H_prod discrimination claim
  (→ W5-1) and the coverage survey covered ~half of
  `CONFORMANCE.md:60` (→ W5-3). Note: the `:280-287` comment this
  entry cites is itself wrong in two of its three clauses (FXC-3);
  the clause this entry quotes is the true, test-pinned one.
- [ ] The shipped `examples/saw-lean/` demo as a replay consumer.
  **AUDITED 2026-07-30, ESCALATED, NOT CLOSED**: emission half
  verified current at HEAD (committed Emitted copies token-identical
  to fresh emission); 8 doc/workflow findings all LOW/INFO; but the
  demo's CI gate provably cannot have been green since 2026-07-18
  (→ W5-2).
- [x] `saw.cabal:41-49` — hand list of shipped kernel files with a
  non-recursive `CryptolToLean/*.lean` glob.
  **CLOSED 2026-07-30**: list exact at HEAD, no subdirectories, no
  dead entries, runtime consumer set closed. Residue: SHIP-1
  (bindist omits data-files, MEDIUM, coupled to W5-2), SHIP-4
  (staging race, CONFIRMED MEDIUM), SHIP-2/3/5/6 LOW.
- [x] Harness improvement: a cross-finding CONSISTENCY check. Wave 3
  simultaneously held "no IO route survives GATE B" (to refute K-3)
  and "an IO route survives" (to confirm K-1). Only the end-stage
  critic caught it.
  **LANDED AND VINDICATED 2026-07-30**: the agent found 4 real
  contradictions (2 factual guard-existence, 2 scoring-discipline)
  and resolved each at the code; two verifier claims were kept out
  of the ledger as a result.

## Release gate — WAVE 2 findings (2026-07-29): STILL DO NOT RELEASE

Report: `doc/2026-07-29_release-gate-audit-wave2.md`. Six Opus lanes
on the surfaces wave 1 said it could NOT establish, adversarially
refuted. 15 findings survived refutation, 5 at CRITICAL/HIGH.

**I re-derived the three most serious claims myself. Two hold; one
does not hold at the severity the verdict assigns it.** The report
leads with that verification, not with the panel's summary.

### BLOCKS RELEASE — confirmed by independent reproduction

- [x] **W2-MAP-1 (CRITICAL, SILENT) — FIXED 2026-07-29,
  mutation-verified.** `emitterBareNames` missed the entire contract
  family. `hardcodedBareNames`
  (`SpecialTreatment.hs`) lists `saw_throw_error`, `vecSequenceM`,
  `atRuntimeCheckedM` and the `saw_fix_*`/`saw_mkStream_*` family, and
  NONE of the ~30 names `Contracts.hs` builds — `intDiv_checkedM`,
  `bvUDiv_runtimeM`, `atWithProof_checkedM`, the 13 `_runtimeM`
  family. VERIFIED by reading both lists. All are emitted unqualified
  and resolve only through the emitted `open`, so the F-7 collision
  gate (`checkEmittedName`) and the F-6 binder-rename seed both miss
  them. A Cryptol definition named `intDiv_runtimeM` therefore
  rebinds the library helper silently.
  This also falsifies TODO's own F-6/F-7 CLOSED entry, which
  describes the enumeration as complete but for `UseMacro`.
  FIX: derive the names from `Contracts.hs` instead of hand-listing,
  so adding a contract row cannot forget to register its name.
  **LANDED.** The complete set now lives in `Contracts.hs` (which
  imports `SpecialTreatment`, not the reverse) and is DERIVED from the
  contract tables, so adding a contract row registers its emitted
  names automatically. The partial set is renamed
  `treatmentDerivedBareNames` so it cannot be mistaken for the whole
  again. Pinned by `saw-boundary/contract_name_collision`.
  **MUTATION VERIFIED:** dropping `contractEmittedNames` from the
  union makes the row exit 0 — silently accepted, exactly the pre-fix
  behaviour.

- [x] **LIB-W2-1 (CRITICAL, SILENT) — FIXED 2026-07-29,
  mutation-verified.** `IntMod` was a reducible constant function, so
  a type-level `unsafeAssert` self-discharged.
  `SAWCorePrimitives.lean:192` is
  `@[reducible] def IntMod : Nat → Type := fun _ => Int`, while
  `Prelude.sawcore` declares `primitive IntMod : Nat -> sort 0` —
  opaque, no reduction rule. VERIFIED by elaboration: all four of
  `IntMod 5 = IntMod 7`, `IntMod 5 = Integer`, free transport of a
  value between them, and the emitted tactic
  `(first | rfl | skip); all_goals sorry` are ACCEPTED with no error
  and **no `declaration uses 'sorry'`**. Negative control
  `Float = Double` (sealed by audit-2 F-2) is REJECTED, so the loud
  path exists and `IntMod` is the outlier.
  `unsafeAssert` is SAW's admission that it has NO proof; the
  backend's stated discipline is that the discharge must prove it.
  Here it is free, and it feeds `coerce` = `cast` on the shared `Int`
  carrier, so a `Z 5` value is reinterpreted as `Z 7`.
  FIX: seal the type family (`structure IntMod (n : Nat) where val :
  Int`, or an `opaque` carrier). **Dropping `@[reducible]` alone is
  NOT sufficient** — a plain `def` is still delta-unfoldable and
  `rfl` still closes. Verified.
  **LANDED** as a `structure`. After the seal all three collapse
  probes REJECT and the emitted tactic leaves `declaration uses
  'sorry'` — the loud path, matching the `Float`/`Double` control.
  Pinned by `negative/intmod_type_collapse` (three probes, ONE CLAIM
  PER FILE).
  **THE CLASS WAS SWEPT, not just the instance.** The shape is:
  SAWCore declares `primitive X : sort 0` (opaque) while Lean aliases
  it reducibly to a shared carrier. There are exactly FIVE such
  primitives. `Float`/`Double` sealed by audit-2 F-2; `IntMod` sealed
  here; `Integer` and `Rational` have the same shape but do NOT
  collapse — each has a distinct carrier and no other SAW type maps
  onto it, `IntMod` being the one that did. The class is closed, but
  closed by coincidence of carrier choice, which is why it is now
  pinned rather than argued.
  **Also fixed the same S-1 MASKING DEFECT in the sibling guard:**
  `negative/float_double_collapse` carried three claims in ONE file,
  so the first failing claim made the row pass while the other two
  could have gone green unnoticed — in the very row that guards the
  F-2 seal. Split one claim per file.
  Two notes: dropping `@[reducible]` alone would NOT have worked (a
  plain `def` is still delta-unfoldable and `rfl` still closes —
  verified); and LIB-3 is unchanged, since `rep` is still a
  representative, not a residue.
  The seal self-test lives in the TEST SUITE, not the library:
  `#guard_msgs` would tie a trust-path file to Lean's exact error
  wording and break on a toolchain bump for a reason unrelated to
  soundness.

### NEEDS REPRODUCTION BEFORE IT IS ACTED ON

- [x] **W2-UNRUN-1 — REPRODUCED BY WAVE 3, FIXED 2026-07-30. The
  "NOT REPRODUCED" analysis below is preserved as a record of how a
  single test case produced a false negative. Everything after
  "ORIGINAL (WRONG) ANALYSIS FOLLOWS" is superseded.** Wave 3 built the shape from ordinary
  Cryptol (`v = [7, error "e"]`, `h = (v @ 0) < 100`, `goal_cut`).
  What follows was my wave-2 reasoning; the fatal error is the word
  "identically" in (i) — the control I ran had a repeated subterm in
  the outermost binder's domain, which hoists the P-1 `let` and
  collapses the emitted arity to 0. Without that repeat the arrow
  survives and the goal EMITS. FIX: goal-shape gate 3
  (`leanExceptCarriedGoalBinders`), pinned by
  `saw-boundary/goal_except_carried_binder_refusal`.
  ORIGINAL (WRONG) ANALYSIS FOLLOWS: The verdict
  leads with "demonstrated end-to-end from ordinary Cryptol with SAW
  exiting 0 on `Theorem (EqTrue False)`". I could not reproduce that;
  both constructible routes are BLOCKED:
  (i) the `goal_cut` script the verdict prints is REFUSED at emission
  — "quantifier telescope mismatch. SAWCore goal binders: 1; emitted
  Lean goal binders: 0" — and the decisive control (a
  hypothesis-bearing goal with NO error anywhere) is refused
  identically, so the pin refuses EVERY sequent-hypothesis goal on
  that route, which is precisely the binder B2 needs emitted;
  (ii) an implication inside the term emits an `@Eq (Except String
  Bool) …` EQUATION, not a Pi, so there is no antecedent to be
  uninhabited.
  The panel's own evidence shows `SAW EXIT: 0` only for a
  `parse_core` term with free variables where `x‵1` is used as a
  TYPE; the pure-Cryptol run shows only "kernel check passed", not
  acceptance of a false theorem. The two look conflated.
  CONSEQUENCE: if real, this is `parse_core`-reachable — the class
  the verdict itself rates HIGH, not CRITICAL — and it does NOT, on
  this evidence, falsify the shipped LIB-1 scope claim as W2-UNRUN-3
  asserts. Both stay OPEN pending a reproduction at the claimed
  reachability. Do not amend the README's LIB-1 scope wording on the
  strength of W2-UNRUN-3 alone.

### WAVE-3 SCOPE — what is logged for the next audit to settle

Recorded here rather than acted on, because acting on an unconfirmed
finding is how a ledger accumulates fiction.

- [x] **W2-UNRUN-1 / W2-UNRUN-3 — SETTLED 2026-07-30: REPRODUCED
  and FIXED, not retracted. Do NOT act on the retraction advice
  below; it is kept only to show what the false negative looked
  like.** See the wave-3 blocker entry above for the fix. Original:
  See the
  entry above for why the claimed ordinary-Cryptol reachability did
  not reproduce. What wave 3 must do, concretely: build a goal whose
  emitted Lean Pi spine has a binder with an `Except`-carried domain.
  I could not construct one — the `goal_cut` route is refused by the
  telescope pin's ARITY half for every sequent hypothesis (verified
  with an error-free control), and the in-term `==>` route emits an
  equation. If wave 3 cannot construct one either, the finding should
  be RETRACTED and the telescope pin's incidental refusal promoted to
  a deliberate, documented one (it is currently load-bearing by
  accident — see W2-UNRUN-4). If wave 3 CAN construct one, the fix is
  the refuse-on-`Except`-carried-binder gate the verdict proposes,
  which costs nothing today: ZERO of 354 artifacts is a
  hypothesis-bearing goal.
  **Do not amend the README's LIB-1 scope wording until this is
  settled** — W2-UNRUN-3's claim that the shipped scope bound is false
  rests entirely on W2-UNRUN-1's reachability.

- [ ] **NEW (mine, 2026-07-29): unapplied `Prelude.coerce` emits
  where every sibling gate rejects.** Found by sweeping the L-1 class
  rather than by the panel. Of the seven `Term.hs` guards that
  conjoin an ident test with an argument pattern, six reject an
  unapplied occurrence (`unsafeAssert`, `error`, `fix`, `MkStream`,
  `if0Nat`, `natCase`); `coerce` emits, exit 0.
  **What I established:** the fact. **What I did NOT establish:** the
  consequence. `coerce`'s guard is a Phase-β LOWERING, not a
  soundness gate, and unapplied it falls through to the faithful
  library `coerce` (= `cast`). So this may be entirely benign. But
  the emitted form is the UN-LIFTED one, carrying `BindingFunction`
  with no record of its formals' representation — which is the F-1
  shape, and F-1 was a real defect. Wave 3 should decide it, and
  should not take my "may be benign" as a finding either way.

- [x] **Convergence proposal §7.1 + §7.3 (2026-07-29): DONE.** The
  three cheap hand-enumeration conversions landed, each
  mutation-verified: `supportLibraryFiles` (directory walk +
  root-import agreement test), `lintForbiddenNames` (derived from
  `TOMBSTONE:` markers at the ten deletion sites), the self-mirror
  ceilings (now exact counts). The replay selftest's waiver list is
  now an evidence-carrying table with dead-waiver, redundant-waiver,
  and evidence checks — whose first run caught two live rots (a
  waiver made redundant by the b1elab case, and a waiver reason
  citing an awk sibling that pins a different property). The
  closure-claim rule is in `contributing.md` ("Closing a defect
  class"). Wave 3's scorecard is proposal §5, updated by this batch:
  the remaining hand enumerations are the two scoped in
  `2026-07-29_unregistered-name-design.md`.

- [x] **NEW (found closing §7.1, 2026-07-29): the cabal invocation
  path of the test gate was silently broken for a month.** Test.hs
  set `SAW="eval saw"`; the two row harnesses that correctly quote
  `"$SAW"` (obligations, differential) ran it as a single not-found
  command, so BOTH categories mass-failed — but only under
  `cabal test saw-core-lean-tests` (the root-Makefile gate). Local
  runs go through `otherTests/saw-core-lean/Makefile`, which sets a
  path, so every green claim since 2026-06-30 was made on the
  working path while the other rotted unwatched. Same class as the
  enumeration failures: two paths, hand-kept in sync, no mechanism.
  FIXED: SAW is now the discovered binary's absolute path (works
  quoted and unquoted), the tasty timeout is a real hang-catcher
  (2400s vs a green sweep's ~22 min; the old 500s could never fit
  one and reported growth as failure), and the canonical gate runs
  green end-to-end (1326s). Residual: nothing asserts the two
  invocation paths stay equivalent — logged for wave 3.

- [x] **Convergence proposal §7.2, pre-wave-3 halves: DONE
  (2026-07-30).** Per `2026-07-29_unregistered-name-design.md`:
  - §3a stage 1: the spelling lint ("every inline `Lean.Ident`
    spelling is registered or a generated binder", SmokeTest) — the
    shadower/reference split is DERIVED from the trailing-underscore
    naming convention, with a companion check pinning the
    convention's blind spot. Its first run found **11 unaccounted
    names** (heads `CryptolToLean`, `Not`, `LT`, `LE`, plus
    `bvNonzeroM`/`ecSignedBVNonzeroM` — checked-contract wrappers
    the contract-derived set missed because they are spelled at the
    point of use — and `succ_macro`, `gen`, `foldr`, `foldl`). All
    registered; the full gate confirms zero corpus churn.
  - §3b both directions: `auditLeanOpaqueDeadEntries` (no dead rows
    today; guards renames/deletions) and
    `auditLeanHandwrittenRealizationOpacity` (9 violations on first
    run, each assessed against its quoted SAWCore body and waived
    with a stated reason in `leanSafeToUnfoldRealizations` —
    sawLet is beta-only, xor/boolEq/is_bvult stop at an opaque
    sibling, bvUExt/bvSExt/rationalZero are differential-pinned,
    seq's unfolding is the intended type-level dispatch).
  All three checks mutation-verified red. REMAINING (post-0.02):
  §3a stage 2, the registry-by-construction refactor of the ~128
  inline spellings. Wave 3 should treat any CRITICAL landing in the
  remaining hand enumerations as CONFIRMING the proposal's
  diagnosis, and any CRITICAL landing in a *derived* enumeration or
  by-construction chokepoint as REFUTING it.

### OTHER SURVIVORS (see the wave-2 report for the full list)

- [x] **L-1 (HIGH, SILENT) — FIXED 2026-07-29, verified both
  directions.** The IntMod modulus gate was bypassed at ZERO
  arguments: the ident-membership test was conjoined with
  `(modArg : _) <- args`, so an unapplied occurrence fell through to
  the ordinary dispatch and emitted a function quantified over all
  `n`, including `n = 0`. Confirmed by running it (exit 0, silent)
  against the applied control (rejects loudly). The membership test
  now stands ALONE with the arity decision inside, so an unapplied
  occurrence gets its own named rejection. Pinned by
  `saw-boundary/intmod_zero_rejection/intmod_unapplied`.
  **THE GENERAL LESSON, recorded because this is a CLASS:** a
  soundness gate written as an argument-PATTERN guard is bypassable
  by supplying fewer arguments, and the bypass is SILENT because
  falling through a guard is how Haskell says "not my case".
  **I swept the other six gates of this shape in `Term.hs`**
  (`unsafeAssert`, `error`, `fix`, `MkStream`, `if0Nat`, `natCase`,
  `coerce`) by running an unapplied occurrence of each. Five reject
  loudly. `coerce` EMITS — see the new open item below.
- [ ] **W2-UNRUN-2 — RE-SCORED 2026-07-31: HIGH → LOW (coverage
  debt, 0.03 carry). The re-score's real product was a separate
  live CRITICAL, now fixed — see the WAVE 5 section.** The filed
  defect stands and is live: the telescope pin's binder-TYPE half
  has zero teeth on hypothesis binders — a Prop-typed binder
  fingerprints `FpOther` on BOTH sides (`sawBinderFp` has no Prop
  arm; `leanBinderFp` heads at `Eq`) and `telescopeFpMismatch`
  skips any position where either side is `FpOther`, so only the
  ARITY half has teeth there. Sharpened by the re-score: the
  fingerprint alphabet cannot EXPRESS a Prop-binder mismatch at
  all, so giving this half teeth would not have caught
  W2-UNRUN-1 and closes nothing by itself. In-model (a gate
  checking less than its text implies), not an evasion route, no
  constructible defect behind it once gate 3 is fixed — LOW.
  0.03 pin sketch: a Prop-vs-value position fingerprint, pinning
  only that a hypothesis STAYS a hypothesis (never its vacuity).
- [x] **OBL-1 / OBL-2 (re-scored MEDIUM by wave 3; FIXED AND
  PINNED 2026-07-31, fast path)** — five stream-helper obligation
  rows shared one byte-identical `expected.txt` naming no stream
  operation; a shift-left→shift-right mutation passed all six
  directives. Now differentiated per operation by lowered
  structure with a verified cross-matrix (each set accepts only
  its own emission); the demonstrated mutation fails on the
  shift_l row's new absents. (OBL-2 was the phantom duplicate,
  removed by wave 3.)
- [ ] **LIB-W2-2 (HIGH)** — `unsafeAssertProofScript`'s stated
  guarantee is not met wherever the two operands are defeq for a
  reason other than being the same assertion; LIB-W2-1 is the live
  instance.
- [ ] Plus MEDIUM/LOW: W2-MAP-2/3, LIB-W2-3..6, OBL-3..7, L-2..5,
  W2-UNRUN-4, W2-CD-1..3 (all three classifyDomain findings were
  REFUTED — that surface came out best and its recorded deferral
  justification was tested and holds).

## Release gate — 0.02 audit findings (2026-07-29): DO NOT RELEASE

Report: `doc/2026-07-29_release-gate-audit.md` (seven Opus lanes, one
per release claim C1..C7; every finding adversarially refuted;
surviving CRITICAL/HIGH given a second independent lens; the audit
itself critiqued for completeness. 21 agents, HEAD 64fb0079c).
29 findings raised, 21 survived refutation, 8 at CRITICAL/HIGH.

**A fix is not closed here until its named PIN lands and the pin's
stated MUTATION has been shown to turn it red.** That rule exists
because this project has shipped vacuous pins repeatedly.

### BLOCKS RELEASE

- [x] **B1/F1 (CRITICAL) — FIXED 2026-07-29, mutation-verified.**
  The trust kernel elaborated the user's Lean BEFORE any gate read it. `replay/lean-check-core.sh:93-94`
  runs `lake env lean` as its first Lean action; the sorry scan
  (`:233-238`) and source lint (`:260-271`) come 140-180 lines later,
  and `Emitted.lean` is in no gate's file list on either path.
  Elaboration executes commands, so a `run_cmd` in `completed.lean`
  runs arbitrary IO while the lint's target AND `Generated.lean` (the
  drift check's authority — the only thing binding the user's `def
  goal` to the SAW obligation) are still on disk and rewritable.
  Result: `CHECK-OK`, `SolveSuccess (LeanReplayEvidence …)` on a
  false obligation. Aggravating: the CI consumer
  (`lean-proof-test.sh`) has the ordering RIGHT, so the product path
  is strictly looser than CI, contradicting `lean-check-core.sh:8`;
  `residual-trust.md` §3.2b reasons from "Emitted is the untouched
  fresh emission", false on this path; and the
  `axiom-or-macro-decl-in-user-file` guard is WAIVED at
  `replay-kernel-selftest.sh:337-355` on the strength of rows that
  only ever carry `proof.lean` — a vacuous waiver.
  FIX: move the pure-text gates above the first Lean invocation;
  then hash the three user files at stage time and re-verify each
  hash immediately before its consuming gate, making "no user
  elaboration precedes any gate on the bytes that gate reads" a
  checked invariant rather than a property of statement order.
  PIN: selftest case on the completed path with a self-erasing
  `run_cmd`, expecting `CHECK-FAIL`; un-waive the guard for that
  path; plus a saw-boundary row driving the payload through
  `offline_lean_replay` so the PRODUCT path is pinned.
  **LANDED.** Two independent changes: the pure-text gates moved
  ahead of the first Lean invocation, AND the ordering became a
  CHECKED invariant rather than a property of statement order — the
  four staged files are digested before anything runs and re-verified
  before the gates the B1 fix covers (`Emitted.lean` at first
  elaboration; `Generated.lean`/`completed.lean` before the drift
  probe; `proof.lean`/`completed.lean` before the re-run text gates
  — NOT before Emitted's post-elaboration grep gates, per the CP-1
  discard; narrowed 2026-07-30, wave-4 DC-1). Plus an assert that the caller's completed-path contract
  (staging the outline as `Emitted.lean` too) still holds, so gate
  coverage cannot silently shrink if `Builtins.hs` changes.
  **MUTATION VERIFIED:** with the pre-fix ordering restored, the
  kernel ACCEPTED the self-erasing payload —
  `FAIL[b1elab]: kernel ACCEPTED a stage the guard
  'axiom-or-macro-decl-in-user-file' must reject`. The CRITICAL
  reproduced in the project's own harness, then closed.
  Four pins, none subsuming another: `b1elab` (ordering, script
  level), `b1hash` (digest guard), `b1contract` (caller contract),
  and `saw-boundary/replay_reject_elaboration_order` (product path).
  Two notes worth keeping. (i) `b1hash`'s first draft used a
  `MUTATE_STAGED_FILE` env hook; that was DROPPED — a dev-override
  affordance inside a trust path is exactly the residual
  `residual-trust.md` §3.2c catalogs. It now provokes the guard
  through the kernel's ordinary inputs, using the fact that
  `Generated.lean` is not covered by the text gates (correct in the
  product, where no user controls it). (ii) the coverage meta-guard
  immediately flagged both new `fail` names as unpinned, which is how
  `completed-path-emitted-not-linted` got a case instead of a
  comment — the meta-guard earning its keep.

- [x] **B2/F2 (CRITICAL) — FIXED 2026-07-29, mutation-verified.**
  F-5's goal-shape gate, recorded CLOSED, missed sorts INSIDE a
  binder's type. `Signature.hs:264-296`:
  classification happens only in `report`, reached only from a
  Lambda/Pi binder's own type; `report`'s fallthrough re-enters `go`,
  whose `Lean.Sort{} -> []` (`:274`) DISCARDS. Gate 1 cannot cover it
  because `Convention.hs:559` matches any `SortContext` before the
  allocating case, so `sort 0` allocates no universe variable.
  `(f : Nat -> sort 0)` emits `(f : Nat -> Type)`; SAWCore admits
  `Prop <= sort 0` cumulativity and covariant Pi subtyping, so the
  SAW obligation ranges over Prop-valued `f` while the Lean goal does
  not — a strictly WEAKER statement, well-typed, no diagnostic.
  Reproduced end-to-end with controls: bare-binder refuses, nested
  BINDER refuses, `sort 1` refuses via gate 1; only `sort 0` at an
  arrow-result position escapes. `parse_core`-reachable only — the
  same class already judged gate-worthy for the bare spelling.
  Two corrections adopted from the second lens: `(v : Vec 3 Type)` is
  NOT reachable (SAWCore rejects it), so scope the fix to the arrow
  case; and the docs' description of the walk is literally accurate —
  what is false is the stated RULE and the `[x] CLOSED` status.
  FIX: in `report`, a binder-type-scoped walk whose `Lean.Sort` arm
  REPORTS instead of falling into `go`'s discarding arm. Scope to
  binder types, NOT all of `go` — `Term.hs:2140`/`:2699` can place a
  `Lean.Sort` in the goal BODY and reporting those over-rejects.
  PIN: `saw-boundary/goal_sort_binder_rejection/sort0_under_arrow.saw`,
  body `\(f : Nat -> sort 0) -> \(x : f 0) -> True`, `.log.good`
  naming `f`. MUTATION: reverting the arm flips it red->green.
  **LANDED** as a binder-type-scoped walk (`goTy`) whose sort arm
  REPORTS. Deliberately not applied to `go`: the goal BODY can
  legitimately carry a `Lean.Sort`, and reporting those would refuse
  faithful emissions. Refuse-only, so over-approximating costs a
  rejected emission and never an admitted one. `make conformance`
  exit 0, so no live over-rejection.
  **MUTATION VERIFIED**, and it exposed a trap the audit's pin spec
  did not name: BOTH outcomes exit 2 — the mutated run exits 2 via
  `prove: 1 unsolved subgoal(s)`, because `offline_lean` is
  emission-only and leaves the goal unsolved. So `.expect-fail` ALONE
  does not discriminate and an exit-code pin here would have been
  VACUOUS. What discriminates is the `.log.good` diff. Recorded in
  the row's own header so a future edit cannot quietly defeat it.
  TRAP (from the audit, still live): an `EqTrue`-terminated variant
  dies earlier in `predicateToProp` and never reaches the gate — the
  goal must be Bool-terminated or the probe is vacuous.

### HIGH — F4 closed; F3/F5/F6/F7/F8 open

- [x] **F4 (HIGH) — FIXED 2026-07-29, mutation-verified.**
  The F-1 `isFunctionShape` sweep missed `Term.hs:466-476`. `(App{}, BindingFunction)` was not swept, so a
  `BindingWrappedArrow` at `foldr`/`foldl`'s `UseArgFunction` slot
  takes the eta-expansion branch and emits a doubly-wrapped ill-typed
  term where the pass-through arm emitted what `foldrM` wants. LOUD
  at Lean (translation succeeds, artifact does not elaborate) so this
  is a capability regression, not unsoundness — HIGH because it
  falsifies the in-tree invariant at `Convention.hs:96-99` and the
  claim in 64fb0079c's own message. Reachable from PLAIN CRYPTOL:
  `{{ foldl (/) (1 : [16]) ([1,2,3,4] : [4][16]) }}`.
  PIN: a `drivers/` row (drivers elaborate) with that Cryptol form.
  **LANDED**, pinned by `drivers/foldl_under_applied_partial`.
  **MUTATION VERIFIED:** reverting `:467` to
  `(App{}, BindingFunction)` reproduces the audit's predicted failure
  exactly — Lean rejects with `v_0 : Vec …` against
  `Except String (Vec …)` at the `bvUDiv_runtimeM` application. Also
  catches dropping `BindingWrappedArrow` from `isFunctionShape`,
  which `under_applied_partial_wrapper` cannot.

- [x] **F3 (HIGH) — FIXED 2026-07-29, mutation-verified.** The snapshot oracle was vacuous over 187 of the
  353 artifacts it counts.** `make conformance` runs only
  differential/obligations/saw-boundary, so the rest are compared
  stale-to-stale by construction. FIX: `.taken-at` marker on
  snapshot; fail loudly on any emitted `.lean` not newer than it;
  correct the script header's `make conformance` to `make test`.
  PIN: oracle self-test requiring STALE for 187 files. MUTATION:
  deleting the freshness guard. Do NOT pin with an emitter mutation —
  the natural candidates also hit a row `conformance` DOES run, so
  such a pin goes red for the wrong reason.
  **LANDED.** `snapshot` writes a `.taken-at` marker; `diff` requires
  every emitted file to be NEWER than it and fails loudly otherwise.
  The script header's procedure is corrected from `make conformance`
  to `make test`. Pinned by a new `selftest` verb, run by `test.sh`:
  it cuts a throwaway snapshot in a temp dir and diffs WITHOUT
  re-emitting, so the guard must fire on every file.
  **MEASURED:** after a conformance-only re-emission the guard reports
  **188 stale files** of 354 — the audit predicted 187, the extra one
  being the F4 row added since. Before the guard, that same diff
  reported "OK: emitted Lean identical".
  **MUTATION:** deleting the guard makes the selftest report OK with
  zero re-emission, and the case goes red.
  NOTE for the record: 585ebf660's inertness CONCLUSION survives —
  the full-suite run plus oracle covered it, and F-1 writes to stdout
  so it moves no `.lean` — but that commit's cited evidence was the
  conformance run, and the attribution was wrong.

- [x] **F5 (HIGH) — FIXED 2026-07-29.** The LIB-1 reference-closure retraction had never
  reached the trust catalog.** `residual-trust.md:669, 680-683` still
  names `differential/vector_literal_edges` as a live escape and
  tells the reader 59 is a FLOOR; the same session established it is
  EXACT. Conservative in direction, but the catalog and the
  correction give a reader opposite bounds on the same shipped
  number. `doc-claim-lint.sh` structurally cannot catch this — the
  named witness exists. Also `b-evidence-design.md:79` arithmetic
  slip and a stale `350`.
  **LANDED** as `support/lib1-census.py`, run by `test.sh` after
  every emission category; it re-derives 59 in-element throwers and 0
  reference-closure escapes instead of re-asserting them. The trust
  catalog's retracted "live witness" sentence is corrected, and it now
  states plainly that the figure bounds THIS CORPUS exactly and is not
  a property of the emitter.
  **Two things came out of BUILDING the pin, neither from the audit:**
  (i) a partial corpus under-reports in the DANGEROUS direction —
  found by making the mistake, scanning mid-sweep gave 27/324 and read
  as good news — so the script asserts corpus SIZE as well; (ii) a
  blind spot the new fold row exposed: the element scan sees a lambda
  in the element slot but not a bare partially-applied name
  (`foldlM … (bvUDiv_runtimeM 16) …`). It does not move the number,
  because a left fold forces every element on both sides so there is
  no unforced-slot divergence — RECORDED rather than patched, since
  widening the scan would move a published figure for a reason
  unrelated to the hazard.
  Also corrects two arithmetic slips, re-derived from the artifact:
  the numeral is `bvNat 8 3`, not `8 1` (`natPos(bit1(one))` = 3), and
  the baseline was 350 then, 353 now.

- [x] **F6 (HIGH) — FIXED 2026-07-29.** `residual-trust.md` §3.3 disowned
  `scLiteralFold`.** It attributes all pre-translation rewriting to
  SAWCore meta-theory, but `Exporter.hs:573` composes that with
  ~130 lines of BACKEND-OWNED hand-written rewriting the Rocq path
  never runs, so "would affect Rocq identically" is backwards. It
  runs UPSTREAM of every pin (`writeLeanProp` computes arity and
  telescope after `scNormalizeForLean`), so nothing downstream
  guards it.
  **LANDED** as §3.3a, its own catalog entry, with §3.3 scoped to the
  SAWCore half it is actually about. Verified independently before
  writing: `scLiteralFold` has exactly 24 rules and a repo-wide search
  finds NO caller outside `scNormalizeForLean`, so "would affect the
  Rocq backend identically" was indeed backwards.
  STILL OPEN, and the entry says so: the per-rule differential rows
  against SAW's own evaluator. Write the guarded partial points first
  (`divNat`/`modNat` at zero, `intToNat` on negatives, `subNat`
  saturation) — those are where a rule and an evaluator most easily
  disagree. MUTATION for that future pin: drop any one guard.

- [x] **F7 (HIGH) — the Slice-7 source lint lost the three new
  modules. FIXED 2026-07-29** (this row went stale-open; caught by
  the wave-5 critic's ledger sweep, gap 4): `lintSourceFiles` in
  `SmokeTest.hs` now ENUMERATES every `.hs` under
  `saw-core-lean/src` at run time, fails loudly on an empty
  enumeration (V-H1 guard), and carries the F7 provenance in its
  own comment. Original filing: a hardcoded 11-file list dropped
  `adaptTo` and `topLevelDefConvention` the moment the 2026-07-29
  module split moved them.

- [x] **F8 (HIGH, ledger) — CLOSED 2026-07-29, and the audit's own
  remedy was wrong.** Owed-pin (ii) IS false: the A-6 guillemet pin
  exists at `trust-tier-selftest.sh` (`debug-escaped`), and I
  re-verified its non-vacuity by mutation rather than on report —
  removing `proof-source-lint.awk`'s `gsub(/[«»]/, "", out)` flips it
  from reject to ACCEPT. Owed entry struck.
  **Where the audit was wrong:** it proposed "give `axiom-escaped` a
  required diagnostic or delete it". A diagnostic CANNOT work. Under
  the same mutation that reddens `debug-escaped`, `axiom-escaped`
  stays green with BYTE-IDENTICAL output, so nothing in the message
  discriminates. The reason is worth keeping: the denylist matches on
  byte boundaries under `LC_ALL=C`, and the guillemet bytes
  (`\xc2\xab`/`\xc2\xbb`) are themselves non-letter boundaries, so
  `«axiom»` satisfies the plain `axiom` rule with or without
  stripping — caught by luck of encoding, not by the fix.
  `«debug».skipKernelTC` differs because the option rule matches a
  DOTTED name, which the interposed bracket bytes break.
  Disposition: KEPT (rejecting the escaped spelling is a real property
  worth holding) with a required diagnostic so it pins its own
  message, and with the claim it cannot support removed from its
  comment. **F8b — CLOSED AS UNCONSTRUCTIBLE 2026-07-31 (the F-9
  treatment; user-accepted fast path — provenance note: the
  clause-2 list proposed "0.03 carry" while this entry's own text
  already said "close it with the F-9 treatment"; the fast-path
  message put the closure option to the user explicitly and the
  closure is what was executed — its own fix audit flagged the
  mismatch, recorded here).** The owed pin's triggering `.saw`
  script cannot be written FOR ANY EMISSION SHAPE REACHABLE TODAY:
  the emitter refuses the shape before the pinned surface is
  reachable (confidence medium per the source audit — "escapes the
  goal-def detection" is an open-ended predicate, not a proof).
  The refusal is upstream of the surface the pin was ordered for
  and is itself pinned (kernel-selftest univgoal;
  `saw-boundary/goal_sort_binder_rejection`). RE-OPEN TRIGGER:
  relaxing the universe gate makes the row possible and required
  (A-9 convention). Canonical owed-pins row (i) struck with the
  same text. Recorded rather than carried: an unconstructible
  obligation in the ledger reads as open debt and distorts the
  clause-2 census.

### MEDIUM / LOW

- [x] **F9 (MEDIUM) — CORRECTED 2026-07-29** (the false justification is struck; the REBASE itself stays open under 'Replay hardening follow-ups'). The single-checker deferral's justification
  was a non-sequitur: the CI harness never invokes
  `lean-check-core.sh`, so "checks are added to the core"
  GUARANTEES drift — the sentence named the mechanism producing the
  drift as the thing preventing it. `goal-formation-trivial` has no
  CI counterpart. B1 is the same shape from the other direction: CI
  had the elaboration order RIGHT while the product path had it
  wrong, so for that check the product was the looser consumer.
  Corrected in `doc/2026-07-16_replay-design.md` with what actually
  bounds the risk today (a trivializing emitter change reddens the
  workflow golden first) — an argument that must be re-made PER
  GUARD, which is why the rebase is the fix.
- [x] **F10 (MEDIUM) — FIXED 2026-07-29, mutation-verified.** `Proof.hs`: `LeanReplayedTheorem`
  absorbs `TestedTheorem`, inverting the assurance lattice, so a
  quickchecked conjunct is reported `verified-lean-replay`.
  Reporting-only, operator-initiated. **LANDED**: clause order IS the
  assurance lattice, and it now reads weakest-first
  (Admitted < Tested < LeanReplayed < Proved). The seventh-audit
  amendment the instance was written for is preserved — Lean replay
  still surfaces over a SOLVER proof, where both are proofs and which
  engine closed it is worth knowing; it was only wrong against
  `TestedTheorem`, which is not a proof at all, so there was no
  dependency to surface and only assurance to lose.
  PIN: four smoketest cases (`assurance lattice (F10)`) rather than
  the audit's suggested summary-JSON row — the suite has no
  summary-JSON category, and the smoketest already links saw-central,
  so the lattice can be pinned exactly and pairwise.
  **MUTATION:** restoring the old clause order reddens EXACTLY the
  pair-specific case and leaves the other three green — so they
  discriminate rather than redundantly assert.
- [ ] **F11 (MEDIUM, docs batch)** — `architecture.md` (A-2/A-9/F-5
  recorded open against a tracker saying closed; module map missing
  seven of twelve modules; `UnrepresentableGoalShape` absent from the
  refusal list); `STATUS.md` (census 14 rows short, and the 0.02 exit
  criterion is quantified over it); imported-realization contract
  absent from the catalog; two uncaveated pointers into an archived
  doc that a maintained doc cites as current.
- [~] **F12 (MEDIUM) — ARGUED 2026-07-29; the successor stays open.** `lean-proof-test.sh`: a
  text regex decides whether the closer-to-authority binding gate
  runs at all, with no in-place argument (unlike the sibling drift
  branch, which has one).
- [ ] **F13 (LOW batch)** — `lean-negative-test.sh:141-146` reports a
  timeout as "elaborated cleanly — soundness drift!";
  `lean-driver-test.sh:179-183` `set -e` leak (latent); orphaned
  Haddock at `Calculus.hs:1136-1152` / `Signature.hs:235-253,
  348-370` — MOVE, do not delete: one block is the sole rationale for
  the gate in B2; stale checkboxes and superseded LIB-1 remedy text;
  the dead `moduleRenamingMap` "Cryptol" target
  (`SpecialTreatment.hs:165`) naming a nonexistent Lean module.

### What this audit did NOT establish — feeds the next wave

- **C2 (loudness) was never assigned to a lane.** Half the charter.
  The next wave must enumerate the fragment boundary FROM THE CODE:
  every `UseReject`/`RejectedPrimitive`/`throwError` site plus every
  default that does NOT reject, showing each non-rejecting default is
  total or provably unreachable.
- **`SpecialTreatment.hs` (1218 lines, 259 mapping entries) was
  opened by nobody.** Its mechanical audits check an entry EXISTS,
  never that the Lean target MEANS what the SAW primitive means. A
  `mapsTo` at a well-typed-but-wrong definition elaborates cleanly:
  silent divergence by construction, the CRITICAL class, on the file
  nobody read.
- **`classifyDomain`'s `otherwise` arm sends unrecognized types to
  `DValue`**, which `shouldWrapBinder` wraps — an unrecognized
  SAWCore type is silently treated as a runtime value rather than
  loudly rejected, the inverse of the stated discipline. Four lanes'
  arguments bottom out in this function as a CONSISTENCY argument
  (two consumers agree), never a correctness one.
- **`lean-obligation-test.sh`'s main path** — 91 rows, ~504 `grep -F`
  substring directives over emitted Lean text, `forbidden.txt` in 0
  of 91 rows, semantic observers in 8 — read by nobody. 83 rows of
  text-shape gating over a semantic object.
- **Nobody compared a Lean support-library body against
  `Prelude.sawcore`.** With the `SpecialTreatment.hs` gap, the
  SAW->Lean MEANING correspondence is unaudited from both ends.
- **Highest-value single probe not run**, endorsed as first after the
  blockers: emit a goal from a sequent that HAS HYPOTHESES
  (`goal_insert`/`goal_intro_hyp`/`goal_cut` -> `sequentToProp`'s
  `scFun` chain) and check the telescope pin and wrap convention on
  the hypothesis binders. Zero rows in 353 artifacts have this shape
  (all 110 goals are bare `Eq`); the telescope pin is PROVABLY blind
  there (a Prop-typed binder fingerprints `FpOther`, so
  `telescopeFpMismatch` skips it and only arity has teeth); and one
  refuter argues it makes LIB-1's admission direction reachable from
  ordinary Cryptol. Recorded UNRESOLVED — the lanes disagreed and one
  probe settles it.

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
below. **2026-07-28: LIB-1 DISPOSITIONED by user decision — ship
documented (README flag + residual-trust §3.2e), no interim gate;
the remedy is the (a) faithful carrier, scheduled with 0.03. It no
longer blocks this release AS A GATE; the defect itself stays open
until (a).**

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
- [x] **S-1 (CRITICAL) — CLOSED 2026-07-25** (05153ef08), by the
  CONTRACT fix (option (a), user-approved), not a checker change:
  no gate can detect a missing obligation when the emitted value is
  defeq without it. The Class-F / Class-S productivity obligations
  were ERASABLE on the completed-outline path — the only path that
  can accept them. `[V]` `saw_stream_realize`'s body was
  `Pure.pure (saw_stream_unfold α x0 step)`, mentioning neither
  `mkfn` nor `_h`, while its own docstring claimed "the proof
  argument is consumed so an undischarged obligation is loud".
  `[V]` `saw_fix_bounded_choose` used `Classical.choice h.seed`
  (Prop-typed ⇒ proof-irrelevant ⇒ ERASABLE); contrast
  `saw_mkStream_choose`, which uses `Classical.choose` (carries the
  predicate as a type-level implicit ⇒ BINDING). So a completed
  outline could write the reduct directly, never stating
  `total`/`lookback`/`faithful`, and drift-`rfl` passed clean.
  Both realizations now draw their value via `Classical.choose` of
  an existential CONTAINING the obligation, so the value cannot be
  written without proving it. Cost, deliberate: the realizations no
  longer REDUCE — "reduces to a proof-free value" and "erasable
  under the defeq drift check" are the same property, so blocking
  the erasure necessarily blocks reduction. The two affected
  observers were rebuilt around the library's propositional
  recovery lemma and are stronger than the `#reduce` they replace
  (`differential/fix_classS_eval`, `proofs/cryptol_module_rec_ones`).
  **Strategy A is INTERIM.** The successor is strategy C (semantic
  per-obligation presence) in
  `doc/2026-07-24_semantic-trust-kernel-plan.md`; A should be
  REVERTED when C lands.

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
  clean kernel. **Row LANDED 2026-07-28:
  `differential/lazy_vector_error_slot`** — the audit's witness run
  through the real pipeline as a pinned known gap: SAW observes
  `true/true/false` (A = 7, B = 9, A ≠ B; the index-1 error thunk is
  never forced), Lean observes `error/error/error` (the
  `vecSequenceM`/`atWithProof_checkedM`/`genWithBoundsM` chain
  collapses every case). The row flips to a rejection pin when the
  (b) fix lands. **Surfaces MEASURED 2026-07-28**
  (`doc/2026-07-28_lib1-scope-measurement.md`): 59 of 350 baseline
  artifacts have a thrower inside an element position — 58 of them
  `atRuntimeCheckedM` (the OP-2 evidence-less indexing route),
  including the whole discharged workflow corpus (s20hash ×32,
  running_sum, popcount, eq_u128, E6). So **(b) at its recorded
  scope is NOT viable** — the "measured cost zero" note was true
  only for user `error`. `genM` is a dead surface (0 uses);
  `foldrM`/`foldlM`/`sawLet` have zero in-element throwers.
  Decision now between (b-narrow) (user-error + runtime-division
  elements only, ~2 rows, leaves the checked-indexing half open),
  (b-evidence), or accelerating (a).
  **(b-evidence) SCRUTINIZED AND REFUTED 2026-07-28**
  (`doc/2026-07-28_lib1-b-evidence-design.md`): five structural
  defects, one foundational — `atRuntimeCheckedM` exists precisely
  where evidence was underivable, so there is no in-artifact
  obligation to admit on; the salvage (minting new per-element
  totality obligations) fails the S-3 emission-time-rejection
  discipline, needs reference-closed interprocedural effect
  analysis (live witness: `vector_literal_edges` let-shares a
  thrower into element spans), and prices at (a)-scale for a worse
  endpoint. Recommendation: (b-narrow) reference-closed as the
  honest stopgap + residual-trust entry for the open half, and
  accelerate (a) resting on the note's kernel-checkable
  `genWithBoundsM_ok_of_total` lemma family.
  **DISPOSITIONED 2026-07-28 (user decision): ship DOCUMENTED — a
  clearly-flagged README section (with the second-party
  "LeanReplayEvidence modulo LIB-1" caveat) + residual-trust §3.2e;
  NO interim gate (both (b) variants rejected: full scope kills the
  corpus, narrow scope closes only the cheapest vector while adding
  gate machinery).** Remedy = (a), scheduled with 0.03; its design
  should start from the salvaged lemma family. Severity assessment
  that informed the decision: a deliberately constructed
  unsound acceptance is demonstrable today and
  Cryptol-reachable, but a narrow false-statement class, zero
  landed proofs affected, and invisible-to-gates by nature (which
  is why documentation, not detection, is the honest interim).

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
- [ ] **Flake: `proofs/llvm_doubleround_comp` reported "emitted .lean
  did not compile — emission drift" under full-suite load**
  (2026-07-26), with only linter WARNINGS in the log and no error.
  Passes standalone. Most likely resource exhaustion — this row
  family is already noted as heavyweight. Worth a real fix rather
  than a shrug: a trust-path harness that intermittently reports
  emission drift without an error is indistinguishable at a glance
  from a genuine drift, which is the one thing that verdict must
  never be ambiguous about. Second heavyweight row this session to
  behave differently in isolation than in the suite.
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
  **CLOSED 2026-07-29** in the Family-3 pass, where it belongs: it is
  the same shape as F-1 — two emissions about the SAME object,
  computed by two different authorities, agreeing only by accident.
  The head now uses `translateIdentToQualifiedIdent`, the call the
  assertion already used. Blast radius as measured, plus the
  hand-written artifacts updated in the same commit.
  **The user-visible price, recorded deliberately:** a discharge now
  writes `@CryptolToLean.SAWCorePrimitives.Num.rec` rather than
  `@Num.rec`. Uniform qualification was chosen over "qualify only
  when the short name is ambiguous" because the latter is DETECTION
  (it needs a model of Lean's root scope) where this is
  by-construction — the F-8 lesson. `@Eq.rec` is unaffected: it
  reaches emission through the hardcoded path F-3b documents.
- [x] **F-6 / F-7 — CLOSED 2026-07-26**, with DIFFERENT treatments,
  because the two halves differ in whether the name is user-facing.
  `emitterBareNames` now enumerates what the emitter writes bare —
  the `UseRename`/`UseRenameUniv`/`UseMapsToWrapped` targets with an
  implicitly-opened (or absent) module, plus a hand-listed set of
  hardcoded emissions.
  * **F-6 RENAMES.** `unavailableIdents` is seeded with that set, so
    `freshVariant` renames a colliding BINDER. Binder names are
    internal to the emitted term. Caught a real instance immediately:
    a goal binder `seq` (from `llvm_fresh_var "seq"`) collides with
    the support library's `seq`, and 32 `llvm_s20hash_comp` goldens
    now read `seq'`. Verified no proof row depends on the old name.
  * **F-7 REFUSES** (`EmittedNameCollision`), at the two sites where
    a SAWCore/Cryptol definition name becomes an emitted declaration
    inside the generated `namespace` — the exact position where Lean
    prefers the local declaration over an `open`ed one SILENTLY.
    Renaming is wrong here: the emitted name is what a user writes
    in a discharge, so `Foo.zip` quietly becoming `Foo.zip'` would
    make their proof reference a name the source never mentions.
    Pinned by `saw-boundary/emitted_name_collision`.
  **Mistake worth keeping:** the first version also listed the
  emitter's own GENERATED binder prefixes (`x__`, `prev_`, `scrut_`,
  the `h_*_` obligation names). Those are the SHADOWERS, not the
  shadowed — listing them renamed the emitter's let-sharing variable
  to `x__'` in every artifact that shares a subterm, failing **77
  rows**. The set is specifically "names the emitter REFERENCES",
  and the code now says so at the site.
- [ ] **S-3 — the Class-F recognizer over-approximates; `inZip` is
  dead code.** `scanRecUses` is entered as `go False elt` and every
  recursive call passes `False`, so the zip arm fires anywhere in the
  element term with no requirement that the zip be consumed by an
  `at` at the inner binder. Converts an intended emission-time named
  rejection into a check-time undischargeable obligation — violating
  the module's own reject-when-unsure discipline, which matters more
  given S-1 undermines "the obligation is the backstop". FIX-SEAM ⇒
  pause rule.
  **ANALYSIS 2026-07-28 (read-only; NOT fixed — the recognizer
  surface is frozen and this entry's own pause rule applies). The
  item is TWO separable halves:**
  1. *`inZip` is dead, provably.* Entry passes `False` (:289) and
     every recursive call passes `False` or routes through
     `goZipSlot` (:321, :337, :342, :351) — there is no `go True`
     in the module. It is a FOSSIL of the pre-sixth-audit design
     (the comment at :314 records that `go True` was replaced by
     `goZipSlot`), so the `then Right True` branch at :306 is
     unreachable and bare-rec-in-a-zip-slot is admitted by
     `goZipSlot`'s own first clause instead. Deleting the parameter
     is therefore BEHAVIOR-PRESERVING — a no-op cleanup, safe under
     the freeze because it cannot change any classification.
     (Pinned meanwhile by the smoketest's "rec use outside zip/at
     slots is Unrecognized", which passes *because* the flag is
     always `False`.)
  2. *The acceptance-breadth defect is real and SEPARATE from the
     flag.* A `zip … rec xs` reached through the generic traversal
     classifies Class F even when nothing consumes it at the inner
     binder — elt[i] then depends on ALL of rec rather than rec[i]
     alone, which is not a lookback-1 recurrence, so the emitted
     productivity obligation was undischargeable where the module's
     reject-when-unsure discipline wanted a named emission-time
     rejection. Not unsound (the obligation is binding post-S-1);
     the cost was discipline.
  **BOTH CLOSED 2026-07-28 (user decision: land the low-risk
  narrowing).** Admission is now STRUCTURAL rather than contextual:
  the flag is gone, the free-floating zip arm is gone, and the
  at-selection matches its rec-containing spine directly — either
  the bare recursive vector or a zip with a BARE rec operand,
  nothing else. Strictly narrowing, so it cannot introduce
  unsoundness. It additionally closes a case the flag design could
  not see: a permuting wrapper ABOVE the zip
  (`at … (reverse (zip … rec xs)) i`), the mirror of the
  wrapper-BELOW case sixth-audit Finding 0 closed — a genuinely NEW
  hole found by the analysis. Gate: all 15 recognizer smoketests
  green unchanged (each traced against the new rule before
  building), full smoketest 73, full suite green with the known-gap
  census unchanged. This is a TIGHTENING, not recognizer growth, so
  it does not breach the 0.03 freeze — growth still requires the
  fragment semantics first.

### Low / housekeeping

- [x] **RK-7 — CLOSED 2026-07-24** (75c2acfc6, C3). The axiom-audit awk output was tested for emptiness
  only, so an awk hard-error reads as a clean audit. `[V]` Confirmed
  asymmetric with the lint invocation, which checks BOTH `lint_rc`
  and output (hardened in the F1 fix). One line.
- [x] **RK-8 — CLOSED 2026-07-25 as documentation.** Cache reuse is
  gated on marker EXISTENCE only; staged contents are never
  re-hashed, so anyone with write access to
  `~/.cache/saw-core-lean/lean-<fp>/` can substitute the support
  library (adding *lemmas*, invisible to the allowlist audit).
  `SAW_LEAN_ROOT` substitutes both library and checker. Both are
  T3 (write access to the library/checker), which the threat model
  puts out of scope — the point of the finding was that an
  out-of-scope boundary left implicit is not documented. Now named
  explicitly in `doc/2026-05-02_residual-trust.md` §3.2c together
  with the toolchain, and with the plain statement of what the
  boundary means: `LeanReplayEvidence` is meaningful to a second
  party only to the extent they trust the environment that produced
  it. No code change — re-hashing the cache would not help against
  someone who can also substitute the checker that does the
  hashing.
- [x] **A-10 — RECONCILED 2026-07-25 in favour of zero tolerance.**
  The two `sorry` rules contradict each other on the completed path
  (the lenient scan of `Emitted.lean` exempts the sanctioned
  in-statement forms; the user-file scan is zero-tolerance; on the
  completed path they apply to the SAME BYTES). Resolution: the
  stricter rule wins, deliberately. The divergence is FAIL-CLOSED —
  it can only refuse a discharge — so it costs completeness, not
  soundness, and the cheap fix (exempt the sanctioned forms in the
  user scan too) would trade a zero-tolerance rule for convenience.
  A completed outline still containing `by sorry` has not discharged
  the obligation the placeholder stands for. Both rules now state
  the contradiction and the decision in `lean-check-core.sh`.
  **The residual is filed where it belongs, below**: a goal whose
  emitted form carries an obligation the user CANNOT discharge is an
  emitter defect, not a checker defect.
- [x] **A-4 — CLOSED 2026-07-25.** `prettyTerm` was the only `Term`
  case producing multi-token output while ignoring `Prec`, so a sort
  in argument position emitted `Vec 5 Type 1` (three arguments to
  `Vec`). Now parenthesised via `sortIsMultiToken`; `Prop` and
  `Type` stay bare since they are single atoms. Note the A-2 gate
  does NOT subsume this: it closes the goal route the audit named,
  but module/term emission still prints sorts at argument position.
  Loud (ill-typed artifact), never silent — fixed because it is two
  lines, not because it threatened soundness.
- [x] **F-1 — CLOSED 2026-07-29** in the Family-3 pass, as that
  family's headline instance. History: claim CORRECTED 2026-07-25 in
  the wrapper design doc; loudness PINNED 2026-07-28
  (`negative/underapplied_partial_illtyped`). The 2026-07-25
  correction named two honest fixes — a wrapped-convention signature,
  or deleting the lowering. **The signature was taken**; deletion was
  ruled out because `differential/cryptol_rev_module` is a live
  consumer, so the lowering is not dead code and deleting it would
  withdraw a working capability.
  Root cause was the binding vocabulary, which is why this is
  Family 3 and not a one-off: `BindingFunction` recorded nothing
  about the formals' representation, so the annotation authority saw
  a Pi-typed SAWCore type, saw a shape that was not `BindingWrapped`,
  and annotated raw over an `Except`-arrow body. Fix:
  `BindingWrappedArrow [ArgMode]` carries the residual argument
  modes, and the annotation became an `AnnotationAdjustment` derived
  from the body's shape instead of a Bool that could only say "wrap
  the whole thing". Mode-DIRECTED, not uniform — a bitvector width
  formal stays a raw `Nat`.
  Evidence, closing the "no compiling witness anywhere in the tree"
  gap the correction recorded: `drivers/under_applied_partial_wrapper`
  (drivers/ rows ELABORATE) with three under-application shapes,
  including the bare three-mode case that would catch a "wrap every
  residual formal" simplification; plus four unit pins in the
  smoketest. The `negative/underapplied_partial_illtyped` probe was
  RETIRED in the same commit — it pinned the loudness of an ill-typed
  emission that no longer exists, and its own text named this fix as
  the reason it would be retired.
- [x] **F-3 (contracts) — CLOSED 2026-07-25 as documentation.**
  Division-wrapper error messages have no SAWCore backing
  (`divNat_runtimeM` throws `"divNat: division by zero"`, which
  SAWCore never produces — unlike the `at` out-of-bounds string,
  which is byte-exact by construction). Both readings of the zero
  point are defensible and the backend takes the simulator's, so
  there is nothing to fix in code; what was missing was the ledger
  saying so. Now recorded in `doc/2026-07-23_fidelity-review.md`
  with all THREE readings of `divNat 2 0` (definitional `1`,
  simulator ⊥, Lean `0`) — the omission was load-bearing in the
  wrong direction, since a future "SAW is undefined there anyway,
  so we may totalize" argument would have reasoned from a false
  premise.
- [~] **LIB-4 — LEAN HALF CLOSED 2026-07-25; SAWCore half open.**
  `saw_ctor_order` compares constructor NAMES in order but says
  nothing about arity or FIELD order within a constructor, and 5 of
  6 asserted datatypes are single-constructor — so the assertion was
  vacuous exactly where the field-order hazard lives. Concretely: if
  `RecordType.RecordValue : α → β → …` drifted to `β → α → …`, then
  at `α = β` (a Cryptol record `{a : [8], b : [8]}` is exactly that)
  the emitted recursor still TYPECHECKS while swapping every
  projection. Closed for the LEAN realization — where the hazard was
  demonstrated — by constructor SIGNATURE pins in
  `SAWCoreCtorOrder.lean`: each `example` ascribes a constructor to
  its expected type, so field order, field types and arity all fail
  loudly at `lake build`. Verified non-vacuous against a
  deliberately field-swapped inductive.
  **Still open: the SAWCore side.** The emitter READS SAWCore's
  declaration, so a SAWCore-side field reorder would be emitted in
  the new order and the Lean pin would still pass. Closing that
  needs the emitter to carry per-constructor field information into
  the emitted assertion (`CtorOrderAssertion` currently carries only
  names).
- [x] **F-3b — CLOSED 2026-07-25 as a documented non-defect.**
  `@Eq.rec` reaches emission through a hardcoded path that skips
  `translateFTermF`, so it carries no ctor-order assertion. Left
  that way deliberately: the assertion catches drift between
  SAWCore's declared order and *this library's* realizing inductive,
  and `Eq` is neither — it is Lean CORE's `Eq`, fixed by the kernel
  and the pinned toolchain. An assertion about it could not fail for
  any reason the mechanism was built to detect, and adding one would
  read as coverage while proving nothing. Recorded in
  `doc/2026-05-02_residual-trust.md` §3.2d.
- [x] **LIB-3 — CLOSED 2026-07-25 as a recorded residual.**
  `IntMod n := Int` means a BOUND `IntMod` variable ranges over
  representatives, not residues — a strictly larger domain.
  Conservative (hence sound) in positive `∀` position; unsound only
  in negative position, and no emitted shape puts a bound `IntMod`
  there. Recorded in `doc/2026-05-02_residual-trust.md` §3.2d
  alongside F-3b, deliberately filed as one of the two survivors of
  the type-image class F-2 belonged to — F-2 showed that class is
  not benign, so its remaining members should not sit unnamed.
  Distinct from the open F1 `n = 0` totalization, which is about
  partiality rather than the domain.
- [x] **F-8 — CLOSED 2026-07-26, by CONSTRUCTION rather than a
  gate.** `combineBinders` took the LAMBDA binder's annotation with
  the PI's result type, and the two are translated by separate
  predicates the code says can disagree. A binder-NAME disagreement
  was already loud (Lean reports an unbound identifier); the
  binder-TYPE half was SILENT, and would give the emitted `def` a
  different type from the SAWCore term it claims to translate — Lean
  cannot catch it, having no idea what the SAWCore type was. Not on
  the goal path, but on `write_lean_term` /
  `write_lean_cryptol_module`, whose defs proofs import.
  Fix: take the PI's binder type. The declared type is the authority
  for what the definition's type is, so the emitted signature now
  has the SAWCore term's type by construction, and a genuine
  disagreement becomes a Lean type error (the body stops matching
  the signature) — loud, and checked by the kernel instead of by us.
  Dropping the body-side annotation is the established pattern, not
  a new one: the unequal-length branch already strips lambda
  annotations wholesale and relies on the signature.
  **A refusal gate was built first and REJECTED — worth recording,
  because the failure is instructive.** Comparing the two renderings
  false-positived twice on one legitimate row: `Eq__rec`'s motive
  rendered `Sort u1` against `Sort u3` (body and type are separate
  traversals drawing from ONE `universeVarCount`, exactly as
  `mkDefinitionWith`'s own docstring says), and `eq_cong` rendered
  `t -> u` against `(_' : t) -> u` (anonymous binder vs unused named
  one). Getting that right needs full structural alpha-equivalence:
  delicate new code in a trust path, to detect a condition one line
  makes unreachable. The machinery was DELETED, not left dormant —
  same reasoning as `lowerFixProofObligation` under S-2.
  Measured cost: ONE golden (`drivers/sawcore_prelude_auto_emit`),
  three cosmetic lines, still elaborating; known-gap count unchanged
  at 71.
- [x] **F-9 — CLOSED 2026-07-25 by REFUSAL.**
  `InjectCodeDecl "Lean"` text went into the emitted file verbatim,
  with no validation and no escaping — an unstructured seam in an
  otherwise fully-structured emitter, landing in `Emitted.lean`,
  which the replay kernel scans LENIENTLY because it is supposed to
  be generator output. Anything could come through: an `axiom`, a
  `set_option`, a `notation` recapturing an emitted name. Refused,
  on the same rule as the other withdrawn surfaces. Cost is zero: no
  public entry point reaches a generic SAWCore-module Lean writer
  (`obligations/injected_lean_code` pins exactly that) and no
  shipped `.sawcore` carries a "Lean" injection. This also ANSWERS
  the open question the CONFORMANCE row recorded — trusted
  declarations or proof-carrying realizations? — in the only
  direction safe by default: not trusted. Admitting them later means
  giving the text a checked shape, not restoring the verbatim copy.
  **The refusal itself is UNPINNED**, and cannot be pinned from a
  `.saw` row: no public entry point reaches the branch. That is the
  same fact that makes the cost zero, so it is stated rather than
  papered over — `obligations/injected_lean_code` pins the
  unreachability, not the rejection. A pin becomes possible (and
  required) the day a public SAWCore-module Lean writer is exposed.
- [ ] **Obligation the emitter cannot discharge** (filed 2026-07-25
  out of A-10's reconciliation). The completed path zero-tolerances
  `sorry`, so a goal whose EMITTED form carries an obligation
  placeholder the user has no route to discharge (the `H_prod`
  placeholder in `fix_classF_eval` is the live case) cannot go
  through it at all. Fixing that in the checker would mean weakening
  a zero-tolerance rule; the defect is that the emitter produces an
  obligation it supplies no way to prove. Belongs with the
  fragment-semantics programme, which is where productivity
  obligations get a discharge route.
- [x] **Printer: drop unused Pi binder names — CLOSED 2026-07-29**
  (filed 2026-07-26 out of F-8). `prettyPiBinder` rendered
  `PiBinder _ (Just x) ty` as `(x : ty) ->` even when `x` is
  unreferenced, so the F-8 fix made three emitted signatures read
  `(_' : a) -> b` where they used to read `a -> b`. Semantically
  identical, uglier, and the right fix was at the printer: a named
  binder nobody references SHOULD print anonymously. Also removes one
  of the two cosmetic axes that defeated the F-8 gate. Measured
  before the fix: 70 occurrences across 9 golden files.
  Landed as `anonymizeUnusedPiBinders`, called from the `Pi` case of
  `prettyTerm`. EXPLICIT binders only — `{x : A}` and `[x : A]` carry
  named-argument and instance-resolution meaning that anonymizing
  would change. Occurrence is decided by identifier STRING over the
  binder's whole scope, so shadowing reads as "used" and the name is
  KEPT: a false "used" costs only the cosmetic status quo, while a
  false "unused" would drop a name a term references, so the analysis
  is deliberately not sharpened past what it can prove.
  Folded into the Family-3 pass rather than a cosmetics batch because
  the emission-convention surface was being restructured anyway —
  which is the opposite of the original filing rationale and the
  better call in hindsight: as a standalone batch it would have been
  9 files of golden churn with no reviewer context.
- [x] **Documentation corrections batch — CLOSED 2026-07-28**
  (survey + spot-checks; doc-claim-lint green corroborates). Every
  listed site had already been corrected by the close that owned it:
  A-3's sites by 75c2acfc6 (C2), the residual-trust reversal by the
  LIB-1 correction block at §3.2a, the `Float`/`Double` argument in
  `SAWCorePrimitives.lean` by F-2, the `divNat 2 0` ledger entry by
  F-3, and `bvSExt` "stays axiomatic" at SAWCorePrimitives.lean:669
  (which now names itself as Phase-9 drift that MISDESCRIBED the
  TCB). F-1's "audited safe" verdict was corrected in the wrapper
  design doc 2026-07-25 and its loudness pinned 2026-07-28
  (`negative/underapplied_partial_illtyped`). Original text kept
  below for traceability.
  ORIGINAL: A-3's five-plus sites
  (including the trust authority); the residual-trust sentence
  LIB-1 shows is BACKWARDS (`:496-503` says the eager carrier makes
  obligations "unprovable, not wrong" — when both sides surface the
  same message the obligation becomes trivially TRUE in Lean while
  FALSE in SAW, and the byte-exact messages chosen to stop Lean
  over-DISTINGUISHING are what let it over-EQUATE); the
  `Float`/`Double` faithfulness argument; the `divNat 2 0` ledger
  entry; `bvSExt` "stays axiomatic"; and the F-1 "audited safe"
  verdict.
- [x] **Dead code — DONE 2026-07-25.** `Lean.Ascription` had only
  consumption sites (pretty-printer, two `Convention.hs` walkers,
  the universe walker) and no construction site anywhere. Deleted
  from the AST and from all five consumers, so it cannot be
  reintroduced without also reintroducing the unguarded-`Prec` case
  the audit flagged. `NatLit` is the other structurally-unguarded
  case; it stays, since every construction site is non-negative —
  noted here so a future negative literal is a known question, not a
  surprise.

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

- [x] Red-before/green-after regression rows for A-1, A-2, A-5 and
  S-1 — CLOSED 2026-07-28 after a coverage audit found most already
  existed (this list predated the closes that carried their own
  pins): R-1 runtime row = `saw-boundary/replay_reject_unbound_completed`;
  A-5 = the kernel-selftest coercion case (drives the real
  `lean-check-core.sh` with the audit's own vector); A-7 lint
  self-test and the notation trust-tier case = present in
  `trust-tier-selftest.sh` since fa842349b.
  **CORRECTED 2026-07-29 (session audit), three claims here were
  wrong:** (i) `replay_reject_unbound_completed` pins R-1 ONLY — it
  stages a `completed.lean`, so the checker takes the
  completed-outline branch and can never enter the plain-path branch
  where A-2's fix lives; **an A-2 runtime pin is still OWED** (see
  the row below). (ii) The trust-tier `axiom-escaped` case is
  VACUOUS for A-6: it rejects identically with and without the
  `gsub(/[«»]/, "", out)` line, because the guillemet bytes already
  satisfy the rule's own delimiters, and it pins no required
  diagnostic — **an A-6 pin is still OWED** (obviated 2026-07-30:
  the D2 narrowing removed the option rule and the gsub with it;
  A-6's subject no longer exists). (iii) The stated reason
  for declining an A-5 RUNTIME row was false; see that row below.
  ADDED
  today: `saw-boundary/replay_reject_notation` (A-1 end-to-end
  through the runtime replay path — the wiring the lint-level cases
  cannot see; rejects `CHECK-FAIL: axiom-or-macro-decl-in-user-file`)
  *(row and token both retired 2026-07-30 with the D2 narrowing —
  this pointer was the third the retirement commit missed, wave-4
  DC-4; A-1's coverage now rides the surviving axiom saw-boundary
  rows for the RUNTIME path, plus the b1elab kernel-selftest case,
  which drives the kernel script directly — kernel-direct, not
  runtime, per this commit's own fix audit)*
  and `negative/fix_obligation_erasure` (S-1: both pre-fix erased
  reducts must fail defeq — the F-2 probe discipline; a
  proof-irrelevant seed or proof-free body returning turns it
  green).
- [ ] **OWED (re-opened 2026-07-29 by the session audit): three
  pins this ledger wrongly recorded as covered.**
  (i) ~~An **A-2** runtime row on the PLAIN path~~ **CLOSED AS
  UNCONSTRUCTIBLE 2026-07-31 (= F8b; this row and the F8b entry
  are the same obligation — the OBL-1 fix audit caught this
  canonical row left open after the F8b entry closed).** Do NOT
  try to build this row: the only way to make it "work" is to
  weaken the emitter gate that closes A-2. The runtime shape is
  unreachable for every emission shape reachable TODAY because the
  emitter refuses it first (confidence medium, per the source
  audit — "escapes the goal-def detection" is an open-ended
  predicate, not a proof); the refusal itself is pinned by
  `replay-kernel-selftest.sh`'s univgoal case and
  `saw-boundary/goal_sort_binder_rejection`. RE-OPEN TRIGGER: a
  row becomes possible AND required if the universe gate is ever
  relaxed (same convention as A-9's stub-site note).
  (ii) An **A-6** lint self-test that
  actually distinguishes the `gsub` guillemet-stripping fix, with a
  required diagnostic (today's case passes on any rejection and is
  byte-identical with the fix removed). (iii) An **A-5** runtime row:
  the earlier decision not to add one was justified by "every
  laundering ingredient is caught by an earlier layer in a way that
  would pin the wrong diagnostic", and that is FALSE — the A-5
  vector passes the source lint and sorry scan untouched and fires
  the CORRECT diagnostic (`axiom-outside-allowlist`), as the
  project's own green selftest log records. The row is worth having;
  the recorded justification for skipping it was refuted.

- [ ] **OWED (created 2026-07-30 by the W2-UNRUN-1 fix): an
  end-to-end row for the telescope pin's ARITY half with a
  carrier-FREE domain.** Goal gate 3 now descends through the P-1
  `let` (the fix audit showed its coverage of that class was
  otherwise accidental), so it fires FIRST on the let-hoisted
  hypothesis shape and SHADOWS the arity half. Consequence:
  `saw-boundary/goal_hypothesis_refusal` no longer exercises the
  arity half — its golden now records gate 3's diagnostic — and no
  other row does either. The arity half is still load-bearing (it is
  the original telescope pin and covers dropped/invented quantifiers
  generally), so leaving it unwatched violates C4.
  PARTIALLY MITIGATED: the `leanPiSpineArity` smoketest cases pin only
  that the FUNCTION scores a hand-built `Let (Pi …)` as 0. They are
  deliberately insensitive to the emitter — corrected here after the
  fix re-audit caught the first version of this entry claiming they
  are "what would break if the hoist behaviour changed". They are not:
  if the emitter stopped hoisting, arities would agree, the arity half
  would silently stop firing end-to-end, and these pins would stay
  green. What is OWED is therefore load-bearing, not tidy-up: a
  runtime row whose SAWCore and emitted arities disagree with NO
  carrier mention anywhere, so gate 3 stays silent and the arity
  diagnostic is the one observed.
- [x] A CI-harness negative row for the no-import decoy-`goal`
  vector (RK-5) — was ALREADY LANDED with the RK-5 close
  (389a55ec9: "Pinned by a decoy-goal case"); the owed entry was
  stale.
- [x] The LIB-1 differential row — LANDED 2026-07-28 as
  `differential/lazy_vector_error_slot` (known-gap pin of the
  SAW `true/true/false` vs Lean `error/error/error` divergence).
- [x] Re-run the appendix witnesses as REAL rows — RETIRED
  2026-07-28: the kernel selftest drives the UNsubstituted
  `lean-check-core.sh` (real `lake`, `CORE=` points at the shipped
  script) with the appendix's A-2/A-5/R-1 vectors, the trust-tier
  selftest runs the A-1/A-6/A-7 lint vectors, and the new
  `replay_reject_notation` row carries A-1 through the full runtime
  path. Nothing exercised under the audit's lake-substitution
  remains unexercised without it. (Row retired 2026-07-30 with the
  D2 lint narrowing — A-1's `notation` ban no longer exists; the
  runtime-path wiring it exercised is carried by the two surviving
  replay_reject_axiom rows and replay_reject_elaboration_order.)

## Release gate (continued)

- [x] **Docs phrasing pass — CLOSED 2026-07-28.** A sweep of the
  maintained docs (README/STATUS/TODO/architecture/cookbook/
  replay-design/calculus/contributing/residual-trust) for
  offensive-security phrasings found the original targets already
  reworked by the intervening doc passes; the survivors are precise
  assurance vocabulary inside finding records ("threat model (T3)",
  "defeated by construction"), which is the intended register. One
  fresh line in the LIB-1 disposition was moved to
  unsound-acceptance vocabulary.
- [ ] **Replay hardening follow-ups** (recorded at replay landing):
  CI-harness rebase onto the factored checker; binder-type
  telescope comparison in the drift check.

## 0.03 program (scheduled, user decision 2026-07-22 — do NOT start early)

- [ ] **GATE-3 REDESIGN: decide hypothesis-vs-value SAWCore-side
  (the D6 revisit item, logged 2026-07-31 with the user decision to
  ship 0.02 on the fourth cut and catalog the residual —
  residual-trust.md §3.2g).** Today's gate RECONSTRUCTS "is this
  telescope domain a folded hypothesis?" from the LEAN image; that
  question was answered wrongly four times in one day (named →
  printed-named → peels-to-carrier → recurse-into-domains), the
  third time after `offline_lean_replay` had ISSUED evidence for a
  false obligation. On the SAWCore side the same question is a SORT
  CHECK — `EqTrue X` is a `Prop`, `Vec 8 Bool` is not — which is
  decidable, does not rot, and is confirmable BY READING. That
  legibility, not a new witness, is the point of the redesign.
  **PROCESS REQUIREMENT, from the record:** design doc first, then
  an ADVERSARIAL review of the design BEFORE implementation (the
  triviality-gate deletion's process, D5), then implement, pin,
  sweep, audit. Four same-day cuts happened precisely because that
  order was skipped under release pressure. Inputs: the four pinned
  witnesses under `saw-boundary/goal_except_carried_binder_refusal`
  (any redesign must refuse all four), the over-refusal probes
  (value / named-used / value→value function must still emit), the
  accepted composite over-refusal, and
  `doc/2026-07-31_why-gate3-escaped.md`.
  Related, same family (fold in): W2-UNRUN-2's `FpOther` telescope
  blindness (LOW) — the fingerprint alphabet cannot express a
  Prop-binder mismatch, which is the same missing distinction seen
  from the other side.

- [ ] **LIB-1 remedy — the (a) faithful per-element carrier**
  (`Vec n (Except String T')`; user decision 2026-07-28 scheduled
  it here when dispositioning LIB-1 as ship-documented). The
  by-construction fix for the carrier collapse: nothing to detect,
  no effect system. Design should rest on the kernel-checkable
  `genWithBoundsM_ok_of_total` lemma family
  (`doc/2026-07-28_lib1-b-evidence-design.md` §"The salvageable
  lemma") and route the representation change through `adaptTo`.
  When it lands: flip `differential/lazy_vector_error_slot` from
  known-gap to true coverage, close residual-trust §3.2e, take
  down the README flag.
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

- [ ] **Unused goal binder emits a file that does not compile
  (found 2026-07-31 by the docs pass).** A goal binder the body never
  references gets a `let <x> := (Pure.pure <x>);` shadow whose type
  Lean cannot infer, so elaboration fails with
  `typeclass instance problem is stuck / Pure (?m.N <x>)`. Minimal
  pair, both over `[8]`: `\(i : [8]) -> i == i` COMPILES;
  `\(i : [8]) -> (3 : [8]) == 3` DOES NOT (the binder is unused).
  With no binder at all, `(3 : [8]) == 3` compiles, so it is
  specifically the unused-and-shadowed case. FAIL-CLOSED —
  `offline_lean_replay` refuses with `emitted-does-not-compile`, and
  `offline_lean` emits a file the user cannot build — so this is
  completeness/diagnostic quality, not soundness. Likely fix: do not
  emit the `Pure.pure` shadow for a binder the body does not
  reference (or annotate it), the same "unused binder" question
  `Pretty.anonymizeUnusedPiBinders` already answers on the type side.
  A user hitting this gets a Lean error with no hint that the cause
  is an unused Cryptol binder, so a named refusal would be better
  than the current stuck instance.

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

- [x] **Split `Term.hs` — DONE 2026-07-29** (SWE-quality review #2;
  was 5,647 lines, now 3,703). Promoted 2026-07-28 into the Family-3
  pass — it was not merely tidying: Family 3's defects live in this
  file, and the split is where the annotation invariant got a home to
  be stated in.
  Worth recording for the next split: "extract `Obligations.hs`" as
  filed is NOT a free cut. Term.hs's 149 top-level definitions
  contain a 56-member mutually-recursive knot, and the `lower*`
  obligation emitters are IN it. What is extractable is exactly what
  the knot does not reach, which a call-graph layering finds:
  `Convention -> Calculus -> Signature -> Obligations -> Term`, zero
  upward edges. `Obligations.hs` therefore holds the obligation
  machinery that is NOT in the knot (proof-carrying application
  builders, the OP-2 Nat interval domain, obligation placeholders);
  the recursive emitters stay put. `Calculus.hs` is the
  "finish the `Convention.hs` split" half — the rules, where
  Convention.hs keeps the vocabulary.
- [x] **Demo proof project's Lean toolchain is STALE, and the drift
  is destructive** (found 2026-07-29 in the Family-3 pass).
  `examples/saw-lean/proof/lean-toolchain` pinned
  `leanprover/lean4:v4.29.1` while `saw-core-lean/lean/lean-toolchain`
  pins `v4.32.0` — and the demo project `require`s the support
  library by RELATIVE PATH, so `lake build` in the demo rebuilt the
  SHARED `cryptol_to_lean` package under 4.29.1 and left the
  suite's oleans unreadable ("incompatible header"); cost a full
  suite run on 2026-07-29 (16 spurious row failures).
  **PIN CONVERGED 2026-07-30 (close-out arc, step 1): the demo now
  pins v4.32.0; `lake build` in `proof/` succeeds and both
  discharges elaborate. Building the demo now builds the shared
  library at the SAME pin the suite uses, so the destructive half
  of this item is structurally gone; the demo README/getting-started
  warnings are retired to a keep-pins-in-sync note.** The separable
  second question — whether the demo should share the library's
  `.lake` build tree at all (a concurrent demo build during a
  sweep still races the suite's artifacts, same-pin or not) —
  remains open below the line as a 0.03-grade hygiene decision, no
  longer a correctness footgun.

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
