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
