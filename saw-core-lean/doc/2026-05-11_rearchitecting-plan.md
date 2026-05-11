# Rearchitecting plan: saw-core-lean as SAW proof tactic

*2026-05-11. Synthesizes the four-agent design pass into a concrete
migration. Replaces the staged plan in
`2026-05-10_compositional-emission-design.md` (which was the
seed thinking; this is the executable plan).*

## Goal

`saw-core-lean` exists exclusively to discharge SAW proof obligations
in Lean's kernel. Mirror the Rocq backend's design point. See
`/Users/miked/.claude/projects/-Users-miked-Projects-claude-lean-saw/memory/project_lean_backend_purpose.md`
for the durable goal statement.

## Companion documents

- `2026-05-10_compositional-emission-design.md` — the architecture
  diagnosis (why we drifted, six-layer model).
- `2026-05-11_target-architecture.md` — concrete target spec (API,
  emitters, file structure, end-to-end discharge flow, soundness
  table). Written by the target-architecture agent.
- `archive/2026-04-22_universe-{problem,internal-investigation,
  external-research}.md` — the parked P4 universe work this plan
  finishes.

## Total budget

**Revised after critic pressure-test (2026-05-11).** Originally
estimated 4.5 weeks; the critic identified that universe handling
and test rebuild were both under-budgeted, and that several
technical gaps the plan didn't address will surface during
implementation (`max 1` rule for inductives, recursor-universe-
ordering, value-position context plumbing, missing `Eq__rec` in
hand-written library, two-pass module walk for forward references,
`isort 1` handling).

**Calibrated budget:**
- **P50 — 7 weeks** of focused work
- **P90 — 12 weeks**
- Plan as-originally-written = P30 optimism

The user has explicitly accepted that the regression suite will
break during the migration; the recovery happens in Phase 6.

**Honest framing:** the parked P4 WIP work claimed "high
confidence" the per-binder-fresh approach handles the universe
gap, but the validation probes were `.tmp/probes/` (gitignored,
never preserved). The proposed per-binder-fresh approach has
**never lived in this repo**, even on the WIP branch (which used
per-level, the failed variant). Phase 0 below is the smallest
gate that validates the architecture before we delete anything.

---

## Phase 0 — Universe approach validation (~0.5 day)

**This is the gate.** Before deleting anything, hand-write a
single Lean file containing the proposed emission shape for
`Eq + Eq.refl + Eq__rec + eq_cong + coerce__def` — the 5-def
slice the universe investigation already analyzed. Run
`lake build`.

- If it elaborates cleanly: the universe approach is validated
  end-to-end against a tiny but representative surface; the rest
  of the plan's risk becomes mechanical.
- If it fails: identify the specific shape Lean rejects. The
  plan needs reshaping before Phase 1 deletes anything.

Validates concretely:
- per-binder fresh universe variables actually work for `Eq__rec`
- explicit `@Foo.{u₀, u₁}` at call sites elaborates
- the `+1` sort shift in `coerce__def` is the right magnitude
- motive-returning-Prop case (in `eq_cong`) doesn't trigger
  Lean issue #2297

Land as `saw-core-lean/lean/intTestsProbe/universe_probe.lean`.
Pin the file as a Phase-2 reference (re-emitting our universe
machinery should produce identical Lean).

## Phase 1 — Deletion sprint (~2 days, REORDERED)

**Critic adjustment:** Phase 1.4 (70 reject deletions) and
Phase 1.6 (`scNormalizeForLean` deletion) moved to **after**
Phase 3.4. Deleting them before auto-emit exists creates a
window where SAW references names with neither SpecialTreatment
nor auto-emit target. Renumbered Phase 4.4 (deletion) and
Phase 5.0 (reject deletions) below.

Goal: remove drift before rebuilding. Five commits, each one
coherent class of garbage.

### 1.1 Delete closed-module probes (~1h)
- `saw-core-lean/lean/intTestsProbe/` — entire directory, all
  `.lean` / `.olean` / `.ilean` artifacts.
- Pinned golden files that exist only to gate closed-module
  emission style.

### 1.2 Delete `offline_lean_skip` plumbing (~2h)
- Primitive in `Builtins.hs:1394+` and `Interpreter.hs:2419+,5286+`.
- `scNormalizeForLean` loud-fail (recent band-aid).
- Breakage: any test using `offline_lean_skip` (deliberate).

### 1.3 Archive drift-era docs (~1h)
- Move to `doc/archive/`: `2026-05-09_release-case-study.md`,
  `2026-05-05_long-term-plan.md`, `audit/2026-05-02_*.md`,
  the three universe archive docs (kept as history, demoted
  from path-of-record).
- Keep: `soundness-boundaries`, `residual-trust`,
  `recursion-design`, `compositional-emission-design`,
  `target-architecture`, and this plan.

### 1.4 Delete dead Lean library bits (~1h)
- Audit `lean/CryptolToLean/Tactics.lean`, `SAWCoreScaffolding.lean`
  for items used only by deleted probes.

*(Former 1.4 — reject entry deletions — moves to Phase 5.0,
after auto-emit exists.)*

*(Former 1.6 — `scNormalizeForLean` deletion — moves to Phase
4.4, after the goal-emission refactor has swapped the pipeline.)*

**Pause/review point** after 1.5: confirm `make test-saw-core-lean`
state reflects the intended baseline (closed-module probes gone,
real proofs still expected to pass).

---

## Phase 2 — Universe rebuild (P4 finish) (~3 days)

Goal: per-binder fresh universe variables + explicit `.{u}` at call
sites + universe-polymorphic hand-library audit. **Precondition
for Phase 3** — the auto-emitted prelude won't elaborate without
this.

Design lives in `2026-05-11_universe-design.md` (universe agent
output, to be saved alongside).

### 2.1 AST + pretty-printer extensions (~0.5d)
- Add `ExplVarUniv :: Ident -> [UnivLevel] -> Term` to
  `Language.Lean.AST`.
- Add `UnivLevel = LevelVar String | LevelLit Natural | LevelSucc
  UnivLevel | LevelMax [UnivLevel]`.
- Update pretty-printer to emit `@Foo.{u, v}`.

### 2.2 `translateSort` split (~1d)
- Split into `BinderPos` / `ValuePos` contexts.
- `BinderPos`: allocate fresh `u_n` per occurrence (never share);
  threaded through `TranslationState`.
- `ValuePos`: emit concrete `Type k`.
- Update `translateBinder'` to use `BinderPos` for bare-`Sort`
  binders; rest stays `ValuePos`.

### 2.3 `mkDefinitionWith` adjustments (~0.5d)
- Switch `_universeVars` to insertion-ordered list.
- Extend `usedUniversesInDecl` for the new `ExplVarUniv` node.
- Verify filter behavior is correct under per-binder fresh.

### 2.4 Call-site level threading (~0.5d)
- New `levelsAtCallSite :: Ident -> [Term] -> m [UnivLevel]`.
- Uses cached `leanSignatureOf` (build incrementally during
  translation).
- Integrates via `useSiteHead` replacing the `Lean.Var`/`Lean.ExplVar`
  emission in `originalDispatch`.

### 2.5 Hand-library universe audit (~0.5d)
- `SAWCorePreludeExtra.lean`: confirm `iteDep.{u}`/`ite.{u}` shape;
  audit `streamScanl`/`cryptolIterate`/`mkStreamFix*` for sort-poly
  arguments.
- `SAWCorePrimitives.lean`: make `coerce` universe-polymorphic
  (`coerce.{u}`); confirm `unsafeAssert` stays monomorphic at sort 1
  per L-2 audit.

### 2.6 `polymorphismResidual` reshape (~0.5d)
- Today: rejects sort-k≥1 binders post-normalization.
- New: translator-internal consistency check ("did the per-binder
  threading produce a Lean kernel-acceptable signature?").
- Renamed `explainUniverseFailure`; called from `UniverseInconsistency`
  exception path, not from the default translation pipeline.
- L-1 *property* preserved (translator either emits universe-
  consistent Lean or refuses loudly); L-1 *trigger* moves.

### 2.7 Smoketest re-bless + universe probes (~1d, EXPANDED per critic)
- Update L-10 smoketest to assert new per-binder-fresh contract.
- **Expand from 3 to ~15 universe probes** covering the
  invariants the critic identified:
  - per-binder fresh (2 distinct `sort 1` binders → 2 distinct `u_n`)
  - `Eq__rec`-shape with motive + carrier → 2-universe def
  - `eq_cong`-shape with two carriers + Prop-returning motive
  - `coerce__def`-shape: monomorphic + body calls universe-poly callee
  - motive returns Prop (u := 0)
  - motive returns sort 1 (u := 1)
  - inductive with sort-0 params (no universe in result)
  - inductive with sort-1 params (`max 1` rule fires)
  - inductive with mixed-sort params (sort-0 absent from universe list)
  - recursor with sort-1 motive on sort-0 inductive
  - recursor with sort-0 motive on sort-1 inductive
  - value-position `Sort k` literal (emits `Type k`, not `Sort u_n`)
  - `UniverseInconsistency` fires on unresolvable arg
  - forward reference (def A calls def B that's emitted later)
  - `isort 1` binder (passes through as `Sort u_n`, no Inhabited synth)
- Reconstruct the ~100-error parked P4 WIP probe set under
  `otherTests/saw-core-lean/universe/`.

**Pause/review point** after 2.7: smoketest passes; full regression
suite still has Phase-1 breakage but is no worse.

---

## Phase 3 — Auto-emit prelude machinery (~5 days)

Goal: `writeLeanSAWCorePrelude` and `writeLeanCryptolPrimitivesForSAWCore`
mirroring the Rocq exporters. **Phase 2 must be complete.**

### 3.1 `SAWCoreLean/SAWModule.hs` (~2d)
- Mirror `saw-core-rocq/src/SAWCoreRocq/SAWModule.hs`.
- Walk SAWCore module, translate each def via `translateTerm`.
- Opaque-recursor handling via existing L-3 gate (Term.hs):
  recursors of mixed-sort inductives become `axiom` emissions.
- Inductives translate via the existing `Lean.Inductive` AST.

### 3.2 `writeLeanSAWCorePrelude` exporter (~1d)
- New function in `Prover/Exporter.hs`, mirror lines 1594–1610.
- SAWScript primitive `write_lean_saw_core_prelude`.
- Test: emit, `lake build` standalone, zero errors.

### 3.3 `writeLeanCryptolPrimitivesForSAWCore` (~1d)
- Mirror line 1612.
- Imports the just-emitted SAWCorePrelude module.
- SAWScript primitive `write_lean_cryptol_primitives_for_saw_core`.

### 3.4 Test harness wiring (~1d)
- `make build-lean-prelude` target emits both into
  `lean/CryptolToLean/Auto/`.
- CI gate: auto-emitted files elaborate.
- Regression tests: auto-emitted Vec/Nat recursors are `axiom`-shaped
  (pins L-3 / L-4 / L-9 survival).

**Pause/review point** after 3.4: auto-emitted preludes elaborate
standalone. Goal-emission still uses `scNormalizeForLean` (delete
that next).

---

## Phase 4 — Goal-emission refactor (~2 days)

Goal: change `writeLeanProp`/`writeLeanTerm` to translate goals as
references; resolve via auto-emitted prelude.

### 4.1 Remove `scNormalizeForLean` from goal path (~0.5d)
- Drop the call in `writeLeanProp` (Exporter.hs:1447) and
  `writeLeanTerm` (line 1398).
- Populate `polymorphismResidual`'s auto-emit allow-set from the
  Phase 3 output.

### 4.2 Move `scNormalizeForLean` to opt-in tactic (~0.5d)
- New SAWScript primitive `normalize_for_lean : [String] ->
  ProofScript ()`.
- L-6 cap survives in this opt-in path.

### 4.3 Update emission preamble (~1d)
- Every goal-emission imports
  `CryptolToLean.Auto.SAWCorePreludeAuto` +
  `CryptolToLean.Auto.CryptolPrimitives`.
- Existing demos regenerate with new imports.

### 4.4 Delete `scNormalizeForLean` infrastructure (~3h, MOVED from Phase 1.6)
- The function itself, `scLiteralFold`, `iterateNormalizeToFixedPoint`,
  `scNormalizeForLeanMaxIters`, `leanOpaqueBuiltins`,
  `leanOpaqueBuiltinsIntentionallyUnmapped`, `discoverNatRecReachers`,
  `discoverEnumEncodingReachers`, `dumpLeanResidualPrimitives`,
  `auditPreludePrimitivesForLean`,
  `auditOpaqueBuiltinsCoveredBySpecialTreatment`.
- ~750 lines from `Prover/Exporter.hs`.
- Safe now: goal pipeline (4.1) and opt-in path (4.2) no longer
  reference these.

**Pause/review point** after 4.4: some demos pass end-to-end through
new pipeline; failures cluster on missing Layer-1 coverage.

---

## Phase 5 — SpecialTreatment shrink (~3 days, RESTRUCTURED per critic)

Goal: prune from ~256 to ~40 entries. Keep only Layer-3 essentials.

**Critic adjustment:** the "delete if matched in auto-emit" audit
direction is wrong — `Stream`, `Pair_fst`/`Pair_snd`, BitVec
operators are all matched in auto-emit BUT must keep their override
because the hand-written Lean side has `@[simp]` annotations, case-
permutation, or native-type mapping the auto-emit can't reproduce.
Phase 5 redesigned as a **positive allow-list**.

### 5.0 Delete drift-era reject entries (~3h, MOVED from Phase 1.4)
- ~70 `reject` entries pointing at SAW-prelude defs that auto-emit
  now covers (SMT-array stubs, with-proof Vec variants, SAW-internal
  proof primitives, bv-equation lemmas, proof axioms).
- Safe now: auto-emit produces the targets, references resolve.
- Keep ALL Layer-3 overlays (untouched in this commit).

### 5.1 Build explicit allow-list of ~40 Layer-3 entries (~0.5d)
Categorize each surviving entry by Layer-3 reason:
- **Native-type mapping (~12)**: Bool, Nat, Integer, String → Lean
  core; BitVec → Lean.BitVec; Vec → Vector; Stream → custom.
- **Soundness overrides (~10)**: iteDep/ite (L-7,16); error/
  error_unrestricted (L-17); coerce shape (L-8); unsafeAssert shape
  (L-2); fix reject (L-5); recursor opacity (L-3).
- **Corecursion lowerings (~5)**: StreamCorec, PairStreamCorec,
  BoundedVecFold, polymorphic-iterate, streamScanl.
- **Datatype adapters (~8)**: Pair, Either, UnitType, RecordType,
  EmptyType, IntMod, Rational, Float — hand-tuned Lean form has
  `@[simp]` lemmas or smaller compile cost than auto-emit.
- **Class dictionaries (~5)**: if Cryptol class-dict surface needs
  hand-tuning.

### 5.2 Delete everything not on the allow-list (~1d)
- Walk SpecialTreatment.hs; delete any entry not in 5.1's list.
- Per-deletion validation: re-emit driver tests exercising the
  constant. If auto-emit form passes, deletion sound. If fails,
  the constant joins the allow-list as a new Layer-3 entry.

### 5.3 Pin residual ST as Layer-3 overlay (~0.5d)
- Document ~40 remaining entries against the 5 categories.
- Update `doc/2026-05-02_residual-trust.md` by-layer.
- Narrow L-14 auto-detect scope: it now checks the allow-list
  itself + verifies every name has both an auto-emit target and a
  Lean-side override. L-14 *property* (no silent unmapped names)
  preserved; trigger reshapes.

### 5.4 Verify Layer-3 soundness gates (~0.5d)
- L-7, L-16: iteDep/ite case-swap regression still fires.
- L-17: error two-tier regression still fires.
- L-2, L-8: unsafeAssert/coerce shape regression still fires.
- L-5: fix rejection regression still fires.

### 5.5 Verify cross-coupling preserved (~0.5d, CRITIC)
- `Stream` override stays: hand-written corecursion library still
  resolves through SAWCorePrimitives.Stream, not auto-emit Stream.
- `Pair_fst`/`Pair_snd` overrides stay: `@[simp]` annotations
  required for downstream proofs.
- `bvAdd`/`bvXor`/`bvShl`/`bvShr`/`rotateL`/...: every entry
  resolves to Lean.BitVec ops, not Vec-of-Bool emission.

---

## Phase 6 — Test rebuild (~6 days)

The user said breakage is acceptable during migration; this is where
we recover.

### 6.1 Reactivate driver tests (~3d)
- One at a time. ~40 drivers; per-test ~30-60min.
- Most failures: missing imports (Phase 4.3 added two) or proof-side
  `unfold` where `scNormalizeForLean` inlined.
- Priority: simple smoke tests → records/tuples/sequences → Cryptol
  modules → LLVM verify drivers.

### 6.2 Reactivate proof tests (~1d)
- E1–E7, llvm_*_eq, cryptol_*_eq.
- Re-bless `.diff` files; adjust `unfold` lists.

### 6.3 ChaCha20 core compositional regression (~0.5d)
- The validating end-to-end: 8 qround overrides + `core` verify +
  Lean discharge of the override-driven obligation.
- New driver: `proofs/llvm_chacha20_core_compositional/`.
- This is the test that proves the architecture delivers.

### 6.4 Enigma involution probe (~0.5d, optional charm)
- 1-char involution via the compositional pipeline.
- New driver: `proofs/cryptol_enigma_involution/`.

### 6.5 Delete closed-module-only tests (~0.5d)
- Tests that exist only for closed-module emission.
- ~5-10 deletions expected.

### 6.6 Property-based hostile-prover re-run (~1d)
- L-1 through L-17 fuzz suite over new pipeline.
- Zero regressions expected; any surface = Phase-3-or-5 soundness gap.

---

## Phase 7 — Doc consolidation (~2 days)

### 7.1 Architecture doc rewrite (~0.5d)
- `doc/architecture.md` around the six-layer model.
- `README.md` opening: "Lean as SAW proof tactic."

### 7.2 Residual-trust catalog reorganize (~0.5d)
- `doc/2026-05-02_residual-trust.md` by layer; each item has layer tag.

### 7.3 Mark drift docs archived (~0.5d)
- Move items not already in `doc/archive/`.
- Update `doc/archive/README.md` with the architectural shift note.

### 7.4 Soundness-boundaries update (~0.5d)
- `doc/2026-04-24_soundness-boundaries.md`: update L-1, L-3, L-6,
  L-10, L-14 trigger descriptions.
- Properties unchanged; pinning tests change.

---

## Risk gates

- **Phase 0 (the gate before any deletion).** Universe approach
  validated on the 5-def slice. If `lake build` fails, reshape
  before Phase 1.
- **Phase 2 → Phase 3.** Universe machinery must work on the
  full ~15 probe set before auto-emit walks the SAWCore prelude.
- **Phase 3.4 → Phase 4.** Auto-emit Layer 1 elaborates standalone
  (hard CI gate). If failing on a specific shape, expect a 1-2 day
  diagnose-and-fix sub-loop. P90 budget for this: 18 days (vs
  plan's 5).
- **Phase 5 audit.** Positive allow-list mitigates wrong-direction
  deletions (cross-coupling overrides like Stream stay).
- **Phase 6.3 ChaCha20 compositional test.** Validating end-to-end.
  Allocate full day for diagnosis if doesn't discharge.

## Lean toolchain pinning (CRITIC)

The plan depends on:
- Lean 4's auto-derived recursor universe-parameter ordering
  (motive first, then params at sort k≥1 only). Convention, not
  spec; could change in a minor version.
- `max u v =?= max u ?v` solvability (Lean issue #2297 status).

Add to Phase 7 docs and CI:
- Pin Lean toolchain version in `lean/lean-toolchain` (already done).
- CI gate: reject toolchain drift (verify version match at build start).
- Fixture test: assert auto-derived recursor universe parameter
  order for `PairType1`, `Either`, `Eq` matches our expectation.
  Fires loudly if a future Lean version reorders.

## L-1 through L-17 survival summary

| # | Lockdown | Survival path |
|---|---|---|
| L-1 | polymorphismResidual | Trigger reshapes (Phase 2.6); property preserved |
| L-2 | unsafeAssert shape | Untouched (Layer-3) |
| L-3 | recursor opacity auto-derive | Phase 3.1 honors via existing gate |
| L-4 | Vec ctor/rec not reachable | Untouched (Layer-3 BitVec) |
| L-5 | fix rejected at boundary | Untouched (Layer-3) |
| L-6 | normalize cap | Survives in opt-in path (Phase 4.2) |
| L-7 | iteDep/ite case-permutation | Untouched (Layer-3) |
| L-8 | coerce axiom shape | Untouched (Layer-3) |
| L-9 | @-prefix on ctor/rec | Routine in Phase 3.1 |
| L-10 | translateSort universe contract | Replaced by per-binder-fresh (Phase 2) |
| L-11 | escapeIdent safety | Untouched |
| L-12 | writeLeanCryptolModule gate | Stays |
| L-13 | every boundary regression-tested | New tests added each phase |
| L-14 | auto-detect missing ST | Scope narrows (Phase 5.3) |
| L-15 | soundness audit in CI | Untouched; runs over new architecture |
| L-16 | Bool#rec emission swap | Untouched (Layer-3) |
| L-17 | error two-tier | Untouched (Layer-3) |
