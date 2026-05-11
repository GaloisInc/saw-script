# Pre-merge audit — saw-core-lean
*2026-05-06*

## Methodology

Eight parallel audits dispatched, each given the saw binary, a working
test harness (45/45 smoketest passing, all integration tests green at
audit start), and access to a `lake` / `lean v4.29.1` toolchain.
Audits covered: soundness, missing pieces, docs/comments, example
coverage, repo organization, things-to-cut, performance/robustness,
and UX/API. Each audit produced an independent findings report with
file/line citations; this document synthesizes them.

Reproducibility commands (verified at audit start):

```bash
SAW=deps/saw-script/dist-newstyle/build/aarch64-osx/ghc-9.8.2/saw-1.5.0.99/x/saw/build/saw/saw
cd deps/saw-script && cabal test saw-core-lean-smoketest        # 45/45
cd deps/saw-script/otherTests/saw-core-lean && bash test.sh test # all green, 102 s
```

## Headline verdict

**Update 2026-05-06:** P-1 is fixed (see below). All driver tests pass,
including the new `drivers/cryptol_module_dag_sharing/` regression at
N=12. The remaining findings are doc rot, missing test pins, and
dead-code cleanup, none of which is a soundness or correctness blocker
on its own.

## Merge-blocker (RESOLVED 2026-05-06)

### P-1 (CRITICAL) — exponential `translateTerm` blowup — FIXED

`src/SAWCoreLean/Term.hs:802-826` walks the SAWCore term DAG without
memoising on `termIndex`. On hash-consed inputs that share a subterm
across N nested bindings, the walk re-translates the subterm 2^N
times.

**Reproducer** (40-line Cryptol module that doubles a value through N
nested `where` aliases):

| N  | SAW wall | SAW peak RSS | emitted size |
|----|----------|--------------|--------------|
| 12 | 0.76 s   | 210 MB       | 52 KB        |
| 16 | 2.39 s   | 715 MB       | 829 KB       |
| 20 | 34.7 s   | **7.8 GB**   | 14 MB        |

Each +4 levels: ≈16× time and memory. Extrapolated N=24 → ~125 GB,
matching the prior Salsa20 failure mode. The full Salsa20 (8
quarterrounds × 10 double-rounds with shared row/column inputs) is the
exact pattern that explodes.

The Rocq backend already has the fix:
`saw-core-rocq/src/SAWCoreRocq/Term.hs:573-598` (`translateTermLet` +
`scTermCount` + `sharedNames`). The omission is tracked in
`doc/2026-05-05_long-term-plan.md:149` (Task #132, "deprioritize"). It
must not be deprioritized — promote to merge-blocker.

**Fix.** Port the Rocq let-sharing pass, OR add an `IntMap`
cache on `termIndex` returning the previously-translated `Lean.Term`.
Either alone is sufficient.

**Regression test.** Add `drivers/cryptol_module_dag_sharing/` (~50
lines, N=12 doubling chain) with a wall-clock and emitted-size budget
in the harness. Would have caught this pre-merge.

**Resolution (2026-05-06).** The Rocq let-sharing pass has been
ported. New code in `src/SAWCoreLean/Term.hs`: `translateTerm` is
sharing-aware, a fresh `translateTermUnshared` does the actual work,
and `translateTermLet` seeds the shared-name map by walking
`scTermCount` over the body and binding shared subterms to fresh
identifiers. `SAWCoreLean/CryptolModule.hs:translateAndRegisterEntry`
now calls `translateTermLet` on each top-level body so the sharing
pass actually fires. Two Lean-specific divergences from Rocq:

1. The `Let` pretty-printer in `Language/Lean/Pretty.hs` wraps the
   RHS in parentheses. Lean 4's layout-sensitive parser otherwise
   treats a soft break inside the RHS as the body of the let
   (`let x := bvNat 8 \n 111;` mis-parses as
   `let x := bvNat 8; body = 111;`).
2. `translateTermLet` filters out subterms whose `termSortOrType`
   returns `Left Sort{}` — i.e., shared subterms that ARE types.
   Lean's elaborator does not always unfold let-bound names during
   recursor-motive checking, so a shared `Vec n Bool` binding can
   break elaboration even though the let is term-level
   definitionally transparent. Rocq's checker handles this fine.

The new regression `drivers/cryptol_module_dag_sharing/`
(`DagSharing.cry` x0..x12 doubling chain) emits 86 lines with
sharing; without sharing it would be exponentially larger. The
`.lean.good` pins this size as the regression target.

## High-severity findings

### H-1 — CI does not install Lean toolchain for `saw-core-lean-tests`

`.github/workflows/ci.yml:756-785` installs elan/lake only when
`matrix.suite == 'integration-tests'`. The `saw-core-lean-tests` suite
runs `otherTests/saw-core-lean/test.sh`, which invokes
`lean-shape-test.sh` and `lean-proof-test.sh`; per the support
harnesses (Phase A 2026-05-04 redesign), missing `lake` fails LOUDLY,
no silent skip. Net: the suite is either red on every CI push, or
elan is being inherited from somewhere I didn't check. **Fix:** drop
the matrix-suite gate on the install step (or duplicate it for
`saw-core-lean-tests`). Confirm with a CI dry-run.

### H-2 — `recursion_stream_fibs_proof` is missing

The revised plan's L-discipline-2 exit criterion specifies *two*
end-to-end recursion-discharge proofs. Only `recursion_stream_corec`
shipped. The mutual-stream lowering (`mkStreamFixPair`) — the most
semantically delicate Phase 5 path — has driver coverage
(`cryptol_module_stream_fibs`) but no semantic-discharge proof. **Fix:**
add `proofs/stream_fibs_corec/proof.lean` checking
`streamFibs k = expected` for small k.

### H-3 — All `intTests/test_lean_*` doc citations are dead

`intTests/` no longer contains any `test_lean_*` directories (Phase F
consolidation moved them to
`otherTests/saw-core-lean/{shape,saw-boundary,proofs}/`). Stale cites
in: `README.md:124-132`, `architecture.md:104-106`,
`getting-started.md:99-100,129,207,220`, `proof-cookbook.md:162,172`,
`contributing.md:123,158,161,170,180,191`,
`2026-04-24_soundness-boundaries.md:49-54,87-95,117,126,170`,
`2026-05-02_residual-trust.md:69,143,337`,
`2026-05-02_recursion-design.md:355,360,366`,
`2026-05-03_stress-test-plan.md:36,157`,
`audit/2026-05-02_phase-1a-2-review.md` throughout, plus
`.github/workflows/ci.yml:761-770`,
`drivers/offline_lean_stress/test_offline_lean_stress.saw:4`, and
`SAWCorePrimitives.lean:716`.

The most severe instance is `2026-04-24_soundness-boundaries.md`: it's
the canonical trust contract, and *every* lockdown row's regression-
test citation is now a broken path. The audit chain that the lockdown
principle rests on is dangling. **Fix:** sweep + rewrite all
references. Largest single improvement to the docs surface.

### H-4 — `saw-lean-example/README.md` is severely stale

Describes a "Phase 0" demo where `write_lean_cryptol_module` is
"Phase 2 / future" and `offline_lean` is "Phase 3 / future". The
adjacent `demo.saw` exercises both today; `out/` shows full-quality
emissions. A new user who lands here is misled about what works.
**Fix:** rewrite from scratch.

### H-5 — `intTestsProbe/` orphan directory

`saw-core-lean/lean/intTestsProbe/` is untracked but present on disk
(currently has `case_b/`, an `.olean` build artifact, etc.). Prior
audit (`audit/2026-05-02_usefulness-and-quality.md:129,173`) and
`2026-05-02_post-audit-plan.md:246` both said *delete*. It's still
there, and `getting-started.md:99-100` references it as a place to
"drop a file directly" — a scratchpad masquerading as a feature.
**Fix:** delete the directory and the doc reference, or formalize it
(`.gitkeep` + nested `.gitignore` + a short doc page). Decide before
merge.

## Medium-severity findings

### M-1 — Residual-trust catalog drift on `Bool#rec`

`doc/2026-05-02_residual-trust.md` §3.1 lists `Bool#rec` direct-emission
as "Pending-gate, comment-grade today". The gate has actually shipped
as a hard `RejectedPrimitive` at `Term.hs:767-779`, pinned by
`saw-boundary/boolrec/`. **Fix:** move §3.1 to a "Closed (2026-05-XX)"
appendix entry citing the gate site and test path.

### M-2 — `polymorphismResidual` is a type-only check

Both `writeLeanTerm`, `writeLeanProp`, and `writeLeanCryptolModule`
call the gate on `scTypeOf t'`, not on `t'` itself. The Lambda-side
defensive walk inside `polymorphismResidual` backstops surviving body
lambdas, and the SAWCore meta-theorem that `scTypeOf` reflects all
binder shapes post-normalization carries the rest. No active soundness
gap, but the trust posture deserves an explicit comment at the call
sites so future contributors don't tighten the wrong knob.

### M-3 — `write_lean_cryptol_module` swallows translator errors

`Exporter.hs:1452-1455` uses `putStrLn` for the translator-error path,
not `throwTopLevel`. A `.saw` script that runs the command followed by
a `lake build` will see "success" and elaborate against a corrupt
file. Inconsistent with `writeLeanTerm` / `writeLeanProp` (both use
`throwTopLevel`). **Fix:** replace with `throwTopLevel`.

### M-4 — Class dictionaries (PCmp/PEq/PRing/...) unmapped

Long-term plan §6 keeps this deferred ("only expand surface as case
studies demand"), but the README's "Status" doesn't flag it. A user
with non-trivial polymorphic Cryptol code will hit unknown-identifier
errors at Lean elaboration time without any help text. **Fix:** add a
one-line note to README "What's punted" listing class dictionaries.

### M-5 — Plan-of-record citation chain is broken

README, `architecture.md`, `getting-started.md`, `contributing.md`,
and `archive/README.md` all cite `2026-05-02_post-audit-plan.md` as
plan-of-record; it's been superseded twice (revised-plan, then
long-term-plan). **Fix:** point at `2026-05-05_long-term-plan.md` or
pick a single canonical anchor. Move three superseded plan files
(`2026-05-02_post-audit-plan.md`, `2026-05-02_revised-plan.md`,
`2026-05-02_semantic-testing-investigation.md`) to `archive/`.

### M-6 — Long-tail translator errors are unpolished

`NotSupported`, `BadTerm`, `LocalVarOutOfBounds`, `UnderAppliedMacro`,
`CannotCreateDefaultValue` (Monad.hs:128-135) emit one-line shapes
with no WHY / WHAT-TO-DO. The headline gates (`UnsoundRecursor`,
`RejectedPrimitive`, `polymorphismResidual`) are A/A-/B+ grade; the
long tail is C/D. `LocalVarOutOfBounds` in particular has a known
cause (`Exporter.hs:1366-1376` documents the `llvm_verify` workaround)
that should surface in the message. **Fix:** add WHY/workaround text
for these five constructors, mirror the headline format.

### M-7 — Source comments still carry "Phase N" buildout chatter

`SpecialTreatment.hs`, `Term.hs`, `FixShapes.hs`, `Pretty.hs`, and the
support library carry Phase-N markers, "post-audit", "Slice A.5", and
narrative residue ("Originally dormant pending …"). Keep `L-N`
markers (each pins a soundness invariant); strip Phase-N (dev
history). Specific list captured in the docs/comments audit; aim for
~30-40 comment edits across 10 files.

### M-8 — `cryptol_module_sha512` driver mixes positive/negative

It lives under `drivers/` but is `expect-fail` (refusal test). Belongs
in `saw-boundary/sha512_fix_rejection/` for hygiene. Mixing positive
and negative tests in `drivers/` makes audit reading harder.

### M-9 — `offline_lean_stress` is misleading

It's a coverage-stress (E1-E7 shape regression), not a memory-stress.
Given P-1 above, the name actively misleads. **Fix:** rename, OR fold
in a small DAG-sharing case (N=8 doubling chain finishes in seconds
and would catch P-1 reincarnations).

### M-10 — `streamScanl` realisation has no `rfl` test

`SAWCorePreludeExtra.lean:91-100` hand-mirrors SAW's `streamScanl`.
If SAW's Prelude updates the body, the Lean side silently drifts.
**Fix:** add `streamIdx _ (streamScanl Nat Nat (+) 0 ones) 3 = 3` as
a `rfl` sanity check.

## Low-severity findings (and cleanup recipe)

### Cuts to execute now

The cuts audit identifies ~140-200 LOC of dead Haskell/Lean and
~700-900 LOC of test-suite trim, all low-risk. Highest-leverage:

1. **Stress proofs E1-E7** (`proofs/E*_*/`) and `drivers/offline_lean_stress/`
   — long-term plan §6 ("Pruning list") explicitly says "execute now".
   Concurrently delete the four lemmas in `SAWCorePrelude_proofs.lean`
   that only E4/E5 use (`gen_atWithDefault`,
   `gen_atWithDefault_double_reverse`,
   `atWithDefault_singleton_zero`, `atWithDefault_out_of_bounds`).
2. **AST dead constructors**: `Lean.Variable`, `Lean.Snippet`,
   `Lean.Comment`, `Lean.SortMax1Var(s)`, `Lean.If`, `Lean.Tactic` —
   ~25-30 LOC across `AST.hs` / `Pretty.hs` / `Term.hs`. (`If` /
   `Tactic` are constructed only in dead smoketest cases — drop those
   too.)
3. **`DefSiteTreatment` dead-consumer** (`SpecialTreatment.hs:69-83`):
   the field, the type, and the unused combinators `realize` and
   `rename` — ~30-40 LOC.
4. **Unused Lean defs/lemmas**: `iter`, `iterNat`,
   `streamScanl_zero/_succ`, `ite_eq_iteDep`, `min_nn`/`min_nSn`/
   `min_Snn`, `equalNat_eq_true_imp_eq`, `eq_imp_equalNat_eq_true` —
   ~60 LOC.
5. **Term.hs export trim**: `mkDefinition`, `translateSort`,
   `translateIdentToIdent`, `translateParams`, `translatePiBinders` —
   five lines, zero risk.
6. **Local scaffolding**: `.tmp-phase5/`, `.tmp-phase6/`,
   `.tmp-slice-b/` (gitignored, ~7 MB on disk).

### Cuts that need a policy decision (defer to post-merge)

- Cookbook-named-but-unexercised lemmas in
  `SAWCoreBitvectors_proofs.lean` — either prune AND prune the
  cookbook docs, or add cookbook test coverage.
- `Tactics.lean`'s `saw_unfold` / `saw_to_bitvec` — documented in the
  cookbook, never exercised in any pinned proof. Either pin or cut.

### Coverage gaps worth filling pre-merge

- **No proof for mutual streams** (closes H-2).
- **`llvm_eq_u128_verify` and `llvm_popcount_verify` drivers have no
  Lean discharge proof** — only 2 of 4 LLVM verify drivers carry an
  E*-style proof slot.
- **No tuple proof** — `drivers/tuples` only emit-diffs.
- **`saw-boundary/` is shallow**: no end-to-end SAW-rejection test for
  `fix_unfold` (separate from `fix`), or for `Z#rec` /
  `AccessibleNat#rec` / `AccessiblePos#rec` (smoketest-only).
- **`UnderAppliedMacro` and several other `TranslationError`
  constructors** still lack triggering tests.

### Repo organization

- **Move `saw-lean-example/` and `saw-rocq-example/`** into
  `deps/saw-script/examples/` (which already exists). They're
  saw-script demos; placing them in the vendored repo gets them
  version-controlled and rides any upstream publication.
- **Delete `lean-reverse-example/`**: a generic Lean-only tutorial
  about list reversal with no SAW dependency. Sibling-name with
  `saw-lean-example/` implies a relationship that doesn't exist.
- **Add a `saw-core-lean/.gitignore`** documenting `.tmp-*/`,
  `.lake/`, `*.olean` (root `.gitignore` covers it; local copy makes
  the backend self-contained for future carve-out).
- **Add per-test `timeout` guards** in `lean-elaborate.sh` and
  `lean-driver-test.sh` (`timeout 120 lake env lean ...` etc.).
  Cheap insurance against future P-1 reincarnations.

## What's working as claimed (positive evidence)

- All four soundness gates fire and are pinned to regression tests.
- Support library reduced to 4 axioms (Vec↔BitVec round-trip × 2,
  `unsafeAssert`, `error_unrestricted`); zero `sorry` outside
  intentional emitted-goal stubs.
- All five attack probes reject as designed (re-verified end-to-end).
- L-16 follow-up smoketest is real and tight (closes the
  comment-grade gap from the prior audit).
- Phase 8 (axioms → defined) effectively shipped.
- Phase 6 surface (IntMod, Rational, Float, Double, enum) shipped.
- Cases A, B, C, D, E driver+proof slots all delivered (modulo H-2
  for mutual streams).
- Integration suite passes 100% in 102 s wall, 690 MB peak RSS.
- 45/45 smoketest cases pass.
- `:help write_lean_term` / `_cryptol_module` / `offline_lean` all
  return well-formed help blocks.
- L-6 100-iter `scNormalize` cap is loud, smoketested with a
  never-converging mock.
- No TODO / FIXME / XXX markers in current source (one benign
  `XXX duplicate?` import note in `saw-central/Exporter.hs:119`,
  unrelated to the Lean backend).
- Pretty-printer stays linear (no quadratic Doc shapes).

## Pre-merge action list (priority order) — **all closed by 2026-05-07**

| # | Item | Status |
|---|------|--------|
| 1 | **(P-1, CRITICAL)** Memoise `translateTerm` on `termIndex`; add regression `drivers/cryptol_module_dag_sharing/` with budget | **CLOSED** (P-1 commit + dag_sharing driver) |
| 2 | **(H-1)** Wire elan install in CI for `saw-core-lean-tests` | **CLOSED** |
| 3 | **(H-2)** Land `proofs/stream_fibs_corec/` | **CLOSED 2026-05-07** (commit 6501edf6a) |
| 4 | **(H-3)** Sweep all `intTests/test_lean_*` doc cites | **CLOSED** |
| 5 | **(H-4)** Rewrite `saw-lean-example/README.md` | **CLOSED** |
| 6 | **(H-5)** Delete or formalize `intTestsProbe/` | **CLOSED** (gitignored as scratch) |
| 7 | **(M-1, M-3, M-4, M-5)** Doc + error-path fixes | **CLOSED** |
| 8 | **(M-6)** Polish long-tail translator errors | **CLOSED** |
| 9 | **(M-7)** Strip Phase-N comments (keep L-N) | **CLOSED** |
| 10 | **(M-8, M-9)** Re-home `cryptol_module_sha512`; rename `offline_lean_stress` | **CLOSED** |
| 11 | Execute long-term-plan §6 prune list (~700-900 LOC test trim) | **CLOSED** (cuts commit) |
| 12 | Cut dead Haskell/Lean (~140-200 LOC) | **CLOSED** |
| 13 | Add `timeout` guards to integration harnesses | **CLOSED** (`lake-timeout.sh`) |
| 14 | Decide on top-level examples placement | **CLOSED** (moved to `deps/saw-script/examples/`; `lean-reverse-example/` deleted) |

Two follow-on items not on the original list also landed in the same
window: **CG-1** (Cryptol audit gate / default-`UseReject`), **CG-4**
(string primitives), **CG-5** (algebraic-enum reject + record-update
driver), and **#134** (SAW env-var fail-loud in test orchestrator).
See `2026-05-06_cryptol-coverage-gaps.md` for the CG-N status table.

## Notes on what was NOT verified

- Did not run a CI dry-run to confirm H-1 reproduces in GitHub
  Actions; the analysis is from reading the workflow file.
- Did not attempt to construct a fuzzer for M-2 (the type-only
  `polymorphismResidual` check) — the meta-argument is sound but a
  property-based test would tighten it.
- Did not measure `lake env lean` wall clock for an N=20 emitted file
  (would require Lean to swap on a 1.5 GB+ working set).
- `SAWCoreBitvectors_proofs.lean`'s 970+ lines were grep-checked for
  axiom-free proofs but not individually re-elaborated; the
  integration suite covers elaboration end-to-end.
- Did not audit the `saw-rocq-example/` Rocq side (out of scope for
  this Lean backend audit).
