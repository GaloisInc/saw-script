# saw-core-lean: keep/kill map (2026-05-14)

A factoring map for separating the well-designed core from the
in-flight Phase-β `Except String` wrap rule. The goal is to make
it possible to either:

- **(A) Resume Phase-β** — quarantine the wrap-dependent code so
  the audit can finish without touching the stable core, OR
- **(B) Reset Phase-β** — excise the wrap rule and restart the
  encoding question (raw types + selective Option/Except, or
  proof-obligation discharge à la `saw_unsafeAssert`), keeping
  the Rocq-mirror skeleton and support library.

The cut criterion below is the same for both options. Whichever
the user picks, the "keep" set is what survives.

---

## The cut criterion

A piece of code is **wrap-dependent** if any of the following are true:

- Its type signature contains `Except String α` (Lean) or
  `wrapExcept` (Haskell).
- Its name ends in `M` and the Lean signature returns
  `Except String α` (e.g. `genM`, `iteM`, `mkStreamFixM`,
  `cryptolIterateM`).
- It threads `Pure.pure` / `Bind.bind` / `liftRawValue` / wrap-aware
  predicates (`shouldWrapBinder`, `isTypeProducing`,
  `isLikelyWrappedTerm`, `typeArgPositions{,Binders}`,
  `quantifierShadow`, `wrappedVars`) into emission decisions.
- It exists only to compensate for the wrap rule's interaction with
  some other invariant (recursor case binders, motive lambdas,
  quantifier shadowing, eta-expanded partial applications under
  `buildLifted`).

Everything else is **wrap-independent** and survives both options.

---

## Map at a glance

| Layer | Total lines | Keep | Excise | Status |
|---|---|---|---|---|
| `src/Language/Lean/{AST,Pretty}.hs` | 484 | 484 (100%) | 0 | Clean. |
| `src/SAWCoreLean/{Monad,Lean,SAWModule,CryptolModule,FixShapes}.hs` | 937 | ~920 | ~17 (CryptolModule wrap-fixup; Monad reader fields) | Clean enough; minor cuts. |
| `src/SAWCoreLean/SpecialTreatment.hs` | 1119 | ~1090 | ~30 (the `*M`-routing entries: `gen`/`atWithDefault`/`foldr`/`foldl`/`ite`/`error`) | Table architecture survives; ~6 entries change target. |
| `src/SAWCoreLean/Term.hs` | 2241 | ~1180 | ~1060 | See per-section map below. |
| `saw-central/.../Exporter.hs` Lean section | ~600 | ~600 | 0 | Clean. Smoketest broken — see "smoketest" below. |
| `lean/CryptolToLean/*.lean` | ~1943 | ~1650 (85%) | ~293 | Concentrated in 4 ranges. |
| `otherTests/saw-core-lean/{drivers,saw-boundary,shape,proofs}/` | 76 dirs | 52 wrap-clean + 9 rejection + 24 with stale `.lean.good`-regen | 0 deletions needed | The 5 broken proofs are repairable. |
| `doc/` | 14 top-level + 35 archive | 5 live + 1 orthogonal | 7 stale top-level + 8 archive-kill | Major rewrite needed on 4 docs. |

**Headline numbers**: of ~7,300 lines of relevant Haskell + Lean
code, roughly **5,950 (~80%) is wrap-independent** and survives
either factoring path. The wrap-dependent excisions cluster in
~half of `Term.hs` (~1,060 lines) plus ~293 lines in the support
library and ~30 routing entries in `SpecialTreatment.hs`.

---

## Haskell source code

### 1. `src/Language/Lean/AST.hs` — KEEP verbatim

Lean 4 surface-syntax AST. Zero wrap dependencies. The `Tactic`
constructor at L114 (`Tactic String`) is what `saw_unsafeAssert`
uses; keep it under any encoding.

### 2. `src/Language/Lean/Pretty.hs` — KEEP verbatim

Pretty printer. Zero wrap dependencies. Pure mirror of
`Language.Rocq.Pretty`.

### 3. `src/SAWCoreLean/Monad.hs` — KEEP, minor cut

- L42–93 error type: KEEP (`UnsoundRecursor`, `RejectedPrimitive`,
  `UnderAppliedMacro` are encoding-independent gates).
- L95–249 error pretty-printer: KEEP.
- L251–290 monad config / runner: KEEP.

No wrap-specific fields in this file. The wrap-specific `Reader`
fields (`_skipBinderWrap`, `_inRecursorCaseBinder`, `_wrappedVars`)
live in `Term.hs` (`TranslationReader` at L88–153). Remove those
three fields when excising Term.hs wrap dispatch.

### 4. `src/SAWCoreLean/Lean.hs` — KEEP verbatim

All four entry points (`preamble`, `translateTermAsDeclImports`,
`translateGoalAsDeclImports`, `translateCryptolModule`,
`translateSAWModule`) are wrap-independent.

### 5. `src/SAWCoreLean/SAWModule.hs` — KEEP verbatim

Module walker. Dispatches on `atDefSite` treatment. No wrap logic.

### 6. `src/SAWCoreLean/CryptolModule.hs` — KEEP, minor cut

- L17–100: KEEP (module structure, registration, normalize callback).
- **L64–70: EXCISE** — the wrap fixup that wraps closed-value top-
  level types in `Except String`. Removable as a 7-line block.

### 7. `src/SAWCoreLean/FixShapes.hs` — KEEP verbatim

190 lines. Pure recognizer for `Prelude.fix` shapes. The recognizer
returns `FixShape` ADT values; emission of the lowering target
happens in `Term.hs` (which is where the wrap-specific `*M` helper
references live). The recognizer itself is encoding-independent.

### 8. `src/SAWCoreLean/SpecialTreatment.hs` — KEEP most, cut ~6 entries

The table architecture (`DefSiteTreatment`, `UseSiteTreatment`,
combinators, `defaultTreatmentFor` rejecting by default, the
`escapeIdent` Z-encoding, `leanReservedWords`) — all KEEP.

The Cryptol-prelude entries (`Num`/`TCNum`/`TCInf`) — KEEP.

The SAWCore-prelude entries (the bulk of the file) — mostly KEEP.
The following routing entries change target if the wrap rule goes:

| Line | SAW name | Current target | Wrap-independent target |
|---|---|---|---|
| ~590 | `ite` | `iteM` (`UseMacroOrVar` with `liftRawValue`) | `ite` (raw, in `SAWCorePreludeExtra`) |
| ~677 | `gen` | `genM` via `mapsToWrapped` | `gen` via `mapsTo` |
| ~678 | `atWithDefault` | `atWithDefaultM` via `mapsToWrapped` | `atWithDefault` via `mapsTo` |
| ~690 | `foldr` | `foldrM` via `mapsToWrapped` | `foldr` via `mapsTo` |
| ~691 | `foldl` | `foldlM` via `mapsToWrapped` | `foldl` via `mapsTo` |
| ~750 | `error` | `saw_throw_error` macro | (re-decide: `reject`, `Option`, tactic) |

Also remove the `liftRawValue` function (L283–311) and the
`mapsToWrapped` combinator (L329–332) if going to option (B).

### 9. `src/SAWCoreLean/Term.hs` — MIXED (the main excision site)

This is the 2,241-line file that drives the keep/kill question.

**KEEP ranges (~1,180 lines):**

| Lines | What | Why kept |
|---|---|---|
| 1–80 | Module header, imports | Trivial |
| 81–155 | `SharedName`, `TranslationReader` (minus 3 wrap fields), `TranslationState`, `TermTranslationMonad` | Type infrastructure; drop `_skipBinderWrap`, `_inRecursorCaseBinder`, `_wrappedVars` from Reader |
| 196–260 | `askTR`, `localTR`, `reservedIdents`, `SortContext`, `translateSort` | Universe handling is encoding-independent |
| 262–289 | `nextVariant`, `freshVariant`, `withUsedLeanIdent`, `translateLocalIdent`, `withSAWVar` | Identifier helpers |
| 291–308 | `BindTrans`, `bindTransToBinder`, `bindTransToPiBinder` | Translated binder ADT |
| 309–359 | `levelOfArg` | Universe-level inference for `UseRenameUniv` |
| 540–611 | `translateBinder'` | KEEP universe branch (L556–572) and base case; **excise** the wrap-decision logic at L585–602 |
| 605–611 | `translateBinders'` | KEEP |
| 638–653 | `translateBinders`, `translatePiBinders` | KEEP |
| 654–718 | `qualify`, `defaultIdentTarget`, `translateIdentToIdent` | Use-site treatment resolution |
| 723–805 | `translateIdentWithArgs` head: `Prelude.fix` shape dispatch | KEEP the StreamCorec/PairStreamCorec/BoundedVecFold/PolyStreamIterate intercepts; the lowering sites change emission targets |
| 1118–1303 | `lowerStreamCorec`, `lowerPairStreamCorec`, `lowerPolyStreamIterate`, `lowerBoundedVecFold` | **KEEP the recognition + lookup-form rewriting**; **change** the emitted helper names from `mkStreamFixM`/`genFixM`/`cryptolIterateM`/`atWithDefaultM` to their raw counterparts |
| 1305–1330 | `translateConstant` | Pure Rocq mirror |
| 1335–1340 | `combineBinders` | Trivial |
| 1340–1410 | `mkDefinitionWith`, `rebrandUnivs`, `stripType` | Definition construction |
| 1410–1465 | `usedUniversesIn*` helpers | Universe-list filter |
| 1465–1475 | `errorTermM` | KEEP |
| 1473–1580 | `translateRecursorApp` | KEEP the Bool#rec / Nat-rec / Pos-rec / Z-rec / AccessibleNat-rec / AccessiblePos-rec guards (L1730–1758); **excise** the scrutinee-`Bind.bind` wrap logic (L1538–1578) |
| 1677–1799 | `translateFTermF` | Mostly KEEP; **change** `ArrayValue` emission (L1788–1798) to drop `vecSequenceM` |
| 1802–2045 | `translateTerm`, `translateTermUnshared` | KEEP `STApp`/`FTermF`/`App`/`Constant`/`Variable` paths; **excise** the wrap-aware `Pi` branching (L1850–1971) and `Lambda` branching (L1973–2027) — collapse to the simple Rocq-mirror pattern |
| 2047–2115 | `withSharedTerm`, `withSharedTerms`, `mkLet`, `translateTermLet` (minus the wrap-name tracking at L2108–2113) | DAG-sharing infrastructure; KEEP |
| 2148–2190 | `runTermTranslationMonad` | KEEP (drop the 3 wrap-field initializers) |
| 2192–2242 | `translateDefDoc` | KEEP; **excise** the `wrapType` fixup at L2225–2234 |

**EXCISE ranges (~1,060 lines):**

| Lines | What | Why |
|---|---|---|
| 361–365 | `wrapExcept` | Wrap-rule primitive |
| 367–399 | `shouldWrapBinder` | Wrap-rule decision predicate |
| 401–414 | `isVariableHead` | Helper for `shouldWrapBinder` |
| 416–436 | `typeArgPositions` | Used only to skip wrap at type-arg positions |
| 438–461 | `quantifierShadow` | Wrap-rule shadow chain for `∀` |
| 464–484 | `typeArgPositionsBinders` | Lambda-side counterpart to `typeArgPositions` |
| 486–538 | `isTypeProducing` | Used only to decide motive-lambda wrap behavior |
| 585–602 (inside L540–611) | wrap-decision branch of `translateBinder'` | The universe handling stays |
| 612–637 | `translateBindersSelective` | Wrap-skip-position dispatch |
| 750–797 | `buildLifted` | The `Bind.bind` chain assembler |
| 838–1117 | `originalDispatch` lifting logic (the `applied` helper from L887 onward) | Rocq-mirror form is `applied f args = pure (Lean.App f args)` — replace the ~230-line wrap-lifting block with ~3 lines |
| 1118–1303 | (Recognition kept; emission targets change) | See KEEP note above |
| 1538–1578 (inside `translateRecursorApp`) | Scrutinee `Bind.bind` wrap | KEEP the guards above this |
| 1599–1675 | `translateCaseHandler` shadow chain | Wrap-rule shadow logic |
| 2120–2146 | `isLikelyWrappedTerm` | Wrap-rule heuristic |
| 2225–2234 | `wrapType` / `liftRawValue` body fixup in `translateDefDoc` | Wrap-rule closing logic |

**Net Term.hs size after excision: ~1,180 lines** — roughly 1.7×
Rocq's 707-line sibling (still bigger because of the universe-
binder machinery and the fix-shape lowering, which Rocq doesn't
have). The "obviously correct by inspection" target from the
May-5 plan becomes achievable.

### 10. `saw-central/.../Exporter.hs` Lean section — KEEP verbatim

The Lean-related code (~600 lines):

- L519–527: `leanTranslationConfiguration` — KEEP.
- L554–573: `scNormalizeForLean` — KEEP. Encoding-independent.
- L602–735: `scLiteralFold` — KEEP. Encoding-independent.
- L737–745: `scIntegerLit` — KEEP.
- L763–778: `iterateNormalizeToFixedPoint` — KEEP.
- L786–802: `collectConstantNames` — KEEP.
- L814–842: `dumpLeanResidualPrimitives` — KEEP.
- L866–928: `auditPreludePrimitivesForLean`,
  `auditOpaqueBuiltinsCoveredBySpecialTreatment` — KEEP.
- L987–1062: `discoverNatRecReachers` — KEEP.
- L1092–1136: `discoverEnumEncodingReachers` — KEEP.
- L1163–1248: `leanOpaqueBuiltins` list — KEEP.
- L1255–1316: `writeLeanFile`, `writeLeanTerm`, `writeLeanProp` — KEEP.
- L1323–1365: `writeLeanCryptolModule` — KEEP.
- L1445–1461: `writeLeanSAWCorePrelude` — KEEP.

---

## Lean support library

Summary from the dedicated audit: **~85% (~1,650 of ~1,943 lines)
survives a Phase-β reset.** The 16 wrap-dependent declarations
cluster in 4 ranges:

| File | Wrap-dependent ranges | Lines | Action |
|---|---|---|---|
| `SAWCorePreludeExtra.lean` | L73–95 (`iteM` + 3 lemmas), L186–214 (`cryptolIterateM` + `idxFromIterateM`) | ~52 | EXCISE |
| `SAWCorePrimitives.lean` | L535–600 (`genM`, `atWithDefaultM`, `foldrM`, `foldlM`, `vecSequenceM`), L669–694 (`mkStreamFixPrefixM`, `mkStreamFixIdxM`, `mkStreamFixM`), L726–747 (`genFixListBuildM`, `genFixM`), L944–977 (`saw_throw_error`, `saw_unreachable_default`) | ~200 | EXCISE |
| `Emitted.lean` | Whole file (41 lines) | 41 | DEMO — regenerates from translator |

**Everything else KEEP:** all of `SAWCoreVectors.lean` (`Vec`),
`SAWCoreBitvectors.lean` (`bitvector`), the 2 BV↔Vec round-trip
axioms (the only axioms in the entire library), all 32 BV ops,
`gen`/`atWithDefault`/`shiftL`/`shiftR`/`rotateL`/`rotateR`/`foldl`/`foldr`/`zip`,
`streamIdx`/`mkStreamFix`/`genFix`/`mkStreamFixPair`,
`coerce`, `saw_unsafeAssert` tactic + its rewrite lemmas,
`iteDep`/`ite` + `_True`/`_False` permutation lemmas,
`streamScanl`/`cryptolIterate` + their `_zero`/`_succ` lemmas,
the string primitives, and the full `SAWCoreBitvectors_proofs.lean`
(71 theorems) + `SAWCorePrelude_proofs.lean` (~55 theorems).

**Risk note**: `saw_unreachable_default` (L975) is signature-clean
(returns raw `α` via `Inhabited.default`) but currently called
only from wrap-dependent lowerings. Keep it — under option (B)
the new encoding likely still needs a typed default for
unreachable fix-lookup positions.

---

## Tests

Summary from the dedicated audit: **no test uses the Phase-β
monadic helper vocabulary directly.** The only Phase-β residue
in the test suite is references to `error_unrestricted` — an
axiom that was deleted from the library. These references appear
in:

- **5 proof tests** (currently won't elaborate):
  - `proofs/E4_map_id/proof.lean`
  - `proofs/E5_littleendian/proof.lean`
  - `proofs/E6_popcount/proof.lean`
  - `proofs/cryptol_running_sum_eq/proof.lean`
  - `proofs/popcount32_via_bridge/proof.lean`
- **19 driver `.lean.good` files** (will regenerate on rerun;
  not human-edited).
- **1 shape `.shouldfail.lean`** (`shape/error_prop/attack_empty.shouldfail.lean`).

**Recommended regression seed (9 short, wrap-clean proofs):**

| Test | Lines | Covers |
|---|---|---|
| `proofs/offline_t3/proof.lean` | 19 | offline goal |
| `proofs/E2_iteDep_refl/proof.lean` | 20 | iteDep |
| `proofs/E1_bvAdd_comm/proof.lean` | 21 | bv arithmetic |
| `proofs/offline_t4/proof.lean` | 21 | offline goal |
| `proofs/tuple_fst/proof.lean` | 22 | tuple projection |
| `proofs/walkthrough/proof.lean` | 22 | Bool distributivity |
| `proofs/E7_wide_assoc/proof.lean` | 24 | wider bv |
| `proofs/offline_t1/proof.lean` | 26 | offline goal |
| `proofs/E3_point_commutes/proof.lean` | 29 | record types |

Plus all 9 `saw-boundary/` rejection tests (no wrap involvement)
and the 4 `shape/*.shouldfail.lean` attack tests.

**Drivers (40 total)**: 21 are wrap-clean as-is; 19 reference
`error_unrestricted` in their pinned `.lean.good` but the `.saw`
inputs are clean — these will regenerate clean under option (B).

---

## Dead and redundant infrastructure

These are items the keep/kill question doesn't depend on the wrap
decision for — they're stale or unused independent of which path
the user picks, and should be excised either way.

### `smoketest/SmokeTest.hs` (920 lines, currently broken)

`SmokeTest.hs:29` imports `polymorphismResidual` from
`SAWCentral.Prover.Exporter`. **That symbol is not exported** —
checking the export list at `Exporter.hs:12–60` confirms; `grep
-rn polymorphismResidual src/` returns only doc files and the
smoketest's own usage at L29, L458, L469, L474, L476, L490,
L496, L498, L513. The whole smoketest module fails to compile.

Per-section ruling:

| Lines | Group | Tests | Status |
|---|---|---|---|
| L66–148 | `prettyPrinterTests` | 10 | KEEP — wrap-independent pretty-printer tests |
| L149–710 | `translatorTests` (non-Phase-5 portion) | ~22 | KEEP — covers L-3, L-6, L-7, L-9, L-10, L-11, L-14, L-16 lockdown items |
| L458–586 | 5 `polymorphismResidual` test cases | 5 | EXCISE (or restore the gate; see below) |
| L712–880 | Phase 5 fix-shape tests | 4 | KEEP — assertions check substring "mkStreamFix"/"genFix"/"mkStreamFixPair" which match both raw and `M` forms |
| L884–913 | `goalEmissionTests` | 1 | KEEP |

**Concrete fix**: drop the `polymorphismResidual` import (L29) and
remove the 5 test cases at L458, L476, L498, L526, L542, L565
(roughly 130 lines including their boilerplate). That brings the
smoketest from "doesn't compile" to "compiles and runs all ~37
wrap-independent assertions" without touching the wrap decision.
If `polymorphismResidual` later gets restored as a real gate,
the tests can be re-added from version control.

### `.tmp-phase5/` (6.9 MB), `.tmp-phase6/` (144 KB), `.tmp-slice-b/` (8 KB)

All three are gitignored (`.gitignore:6` matches `.tmp-*/`).
Contents are working-phase artifacts:

- `.tmp-phase5/` — Cryptol probes (Factorial, Popcount, RecFib,
  SHA, SHA512, Salsa20Q, Simple), `.saw` drivers, shape `.txt`
  / `.out` analyses, and two emitted `.module.lean` outputs.
  Phase 5 has landed; these are post-mortem artifacts.
- `.tmp-phase6/` — analogous for Phase 6 (Point, Salsa20, comp,
  enum, floatprobe, headtail, intmod, transpose, etc.).
- `.tmp-slice-b/` — leftover from Slice B exploration.

**Action**: `rm -rf .tmp-*` at the project root. Nothing in
version control or in any test path references these. ~7.1 MB
of working detritus.

### `lean/intTestsProbe/` (584 KB, gitignored)

Per `.gitignore:9`. Contains ~40 hand-written `.lean` and `.saw`
probe files from past audits (`gamma_*.lean`,
`saw_unsafeAssert_test.lean`, `vc_attempt.lean`, etc.). Useful as
local debugging scratchpads during development; not referenced
by any test driver or build target. **Action**: same as `.tmp-*`
— `rm -rf` it, restore as needed.

### `lean/Emitted.lean` (the placeholder)

Not dead, just a working file. The integration test harness
(`otherTests/saw-core-lean/support/lean-proof-test.sh:100`)
copies each test's emitted output to this path so the
corresponding `proof.lean` can `import Emitted`. Its current
contents are whatever was last emitted — likely Phase-β-flavoured
today. **No action** beyond noting it's not a stable artifact.

### `archive/README.md`

Already flagged under docs. Cites the (now-archived)
`2026-05-05_long-term-plan.md` as "current plan-of-record"
(L17), which is incorrect since 2026-05-11. Edit or delete.

### Inert constructors and dead code paths

- `UnderAppliedMacro` (`Monad.hs:79`) — structurally unreachable
  today (every `UseMacro` entry uses `n=0`) but kept as a future
  gate per the comment at L73–78. **KEEP** — small and
  documented.
- `errorTermM` (`Term.hs:1468`) — only called from the recursor
  "no-Lean-target" path (`Term.hs:1767`). Likely still needed
  under option (B). **KEEP**.
- The `Lambda.Fix` constructor mentioned in `AST.hs:76–78` was
  preemptively excluded — no dead code, just a documented
  divergence from Rocq. **No action**.

### Dead doc references in code comments

Several `Term.hs` and `SpecialTreatment.hs` comments cite the
archived May-5 plan path (e.g. `Term.hs:1308` cites
`doc/2026-04-23_stage3-translator-sketch.md` which this map
flags as KILL). When rewriting the trust docs (per the docs
section), grep for `doc/202` in `src/` and update the citations.

---

## Documentation

Summary from the dedicated audit: **5 docs are the live reference
set; 6 need rewriting; 8 archive entries are KILL-candidates.**

### Live reference set (KEEP, possibly with date-stamp refresh)

- `2026-05-11_rearchitecting-plan.md` — active migration plan.
- `2026-05-11_target-architecture.md` — concrete target spec.
- `2026-05-11_hand_library_universe_audit.md` — Phase 2.4 result.
- `2026-05-11_universe_stress_targets.lean` — Phase 2.6 probes.
- `2026-05-02_recursion-design.md` — Phase 5; encoding-orthogonal.
- `proof-cookbook.md` — discharge reference; orthogonal.

### Phase-β-specific (KEEP if option A, KILL if option B)

- `2026-05-11_beta_replan.md` — the doc that defines the wrap rule.
- `2026-05-14_wrap-invariant-audit.md` — the in-progress audit.

### Needs rewrite (contradicted by current code)

- `architecture.md` — describes a pre-rearchitecting pipeline.
  Pipeline claims (scNormalizeForLean position, translateSort
  collapse-to-Type) are stale; cites the archived May-5 plan as
  plan-of-record. Rewrite as a "you are here" page or delete.
- `2026-04-24_soundness-boundaries.md` — pins `polymorphismResidual`
  exits (L47–50, L281) that no longer exist in code; pins L-10
  universe contract that `rearchitecting-plan.md:445` replaces;
  inconsistent with `residual-trust.md` on Bool#rec direct-emission
  status (`soundness-boundaries.md:325–327` vs
  `residual-trust.md:368–389`). Major rewrite.
- `2026-05-02_residual-trust.md` — §1.4 inventory cites axioms
  already deleted; §2.3 universe collapse contradicted by
  rearchitecting plan; uncatalogued Inhabited-fallback residual.
  Major rewrite, ideally merged with `soundness-boundaries.md`
  into a single layer-tagged catalog (`rearchitecting-plan.md:387`
  schedules this).
- `contributing.md` — references the archived May-5 plan as
  current. Minor rewrite.
- `getting-started.md` — same. Minor rewrite plus a preamble
  refresh.
- `archive/README.md` — cites an archived plan as current. Edit
  or delete.

### KILL outright (in archive, no current citations, superseded)

| File | Why |
|---|---|
| `archive/2026-04-22_phase-2-design.md` | Superseded; no citations. |
| `archive/2026-04-22_phase-2c-findings.md` | Obsoleted by specialization pivot. |
| `archive/2026-04-23_stage1-depanalysis.md` | One-shot deliverable. |
| `archive/2026-04-23_stage3-translator-sketch.md` | Sketch overtaken by implementation. |
| `archive/2026-05-01_status-and-next-steps.md` | Self-superseded. |
| `archive/2026-05-01_bitvec-binding-decision.md` | Decision inverted by Phase 9. |
| `archive/2026-05-03_stress-test-plan.md` | Plan executed. |
| `archive/2026-05-11_sound-cryptol-semantics-plan.md` | Same-day alternative to `beta_replan.md`; `beta_replan.md:250–253` explicitly rejected its newtype approach. |

### Archive-worthy history (KEEP in archive/, but don't promote)

The remaining ~25 dated files in archive/ are trajectory
documentation. Several are cited from soundness-boundaries /
residual-trust as deep-dive references (e.g. `2026-04-24_audit-nat-mapping.md`,
`2026-04-22_universe-internal-investigation.md`,
`2026-04-22_p4-v2-status.md`). Keep them.

### Missing entirely

- **A `STATUS.md` at top level** that tells a fresh reader "you
  are here" in one page. Right now a fresh reader has to read
  three May-11 plans plus the May-14 audit to understand state.
- **A consolidated residual-trust catalog** post-rearchitecting,
  including the Inhabited-fallback residual.
- **A retraction note** for the May-5 "near-syntactic rewrite"
  principle — either in `rearchitecting-plan.md` or a separate
  one-paragraph addendum.

---

## Two factoring sequences

### Step 0 — Dead-infra cleanup (independent of A vs B)

Do this first regardless of wrap decision. None of these touch the
translator semantics; all unblock subsequent steps.

1. Drop the `polymorphismResidual` import and the 5 referencing
   test cases from `smoketest/SmokeTest.hs` (L29, L458–586).
   Verify with `cabal test saw-core-lean-smoketest` — should now
   compile and run ~37 wrap-independent assertions.
2. `rm -rf .tmp-phase5 .tmp-phase6 .tmp-slice-b` (~7.1 MB).
3. `rm -rf lean/intTestsProbe` (~584 KB).
4. Delete the 8 KILL-outright archive docs (per the docs map).
5. Fix `archive/README.md` (cites archived plan as current) or
   delete it.
6. Grep `src/` for `doc/202` and update stale doc citations in
   code comments.

After step 0 the tree compiles, the smoketest runs, and ~8 MB of
working detritus is gone. This is risk-free cleanup.

### Option A — Keep Phase-β (quarantine without restart)

1. Move `iteM`/`*M` wrap helpers in the support library into a
   single `lean/CryptolToLean/PhaseBeta.lean` so they're visibly
   isolated (a 293-line file).
2. Move the wrap-dispatch ranges of `Term.hs` into a separate
   module `SAWCoreLean.PhaseBeta.Term` (or similar) and have the
   main `Term.hs` either call into it conditionally or unconditionally
   — depending on whether you want a translation-mode flag.
3. Re-sync the trust docs (`soundness-boundaries.md`,
   `residual-trust.md`, `architecture.md`) to current code.
4. Close the 5 stale `error_unrestricted` proof tests (regen `.lean.good`s, edit `proof.lean`s to use whatever the new
   error-handling target is).
5. Resume the wrap-invariant audit.

### Option B — Reset Phase-β (excise the wrap)

1. Branch off. On the branch, apply the EXCISE ranges from this
   document:
   - `Term.hs` ~1,060 lines (per the §9 map above).
   - `SpecialTreatment.hs` ~30 lines (the `*M`-routing entries + `liftRawValue` + `mapsToWrapped`).
   - `CryptolModule.hs` 7-line wrap fixup.
   - `Monad.hs` reader fields (3 unused after Term cuts).
   - `lean/CryptolToLean/{SAWCorePrimitives,SAWCorePreludeExtra,Emitted}.lean` ~293 lines.
2. Replace the `applied` helper in `originalDispatch` (Term.hs
   L887+) with the 3-line Rocq form `applied f args = pure
   (Lean.App f args')` where `args'` is `mapM translateTerm args`.
3. Re-decide the 6 wrap-target SpecialTreatment entries — pick
   one of the three encodings (translation-time reject, selective
   Option/Except, proof obligation) for `error` / `ite` /
   `gen` / `atWithDefault` / `foldr` / `foldl`. The simplest
   first cut is "translation-time reject + ask the user to
   refactor"; this matches Rocq's Phase-1 stance and gets the
   regression suite green for the 18 wrap-clean proof tests
   plus the 9 rejection tests immediately.
4. Update `architecture.md` + `STATUS.md` + the trust docs to
   reflect the new state.
5. Decide if/when to re-attempt a partiality encoding, with the
   wrap-invariant audit's lessons in hand.

---

## What this map does not decide

- **Which option is right.** I've argued elsewhere
  (`2026-05-14_backend-review.md`) that the Phase-β bet is
  plausible but unexecuted. Whether to finish executing it or
  reset is a strategy call. This map only makes both paths
  cheaper to take.
- **What replaces the wrap rule under option B.** Three
  candidates: (a) translation-time reject, (b) selective
  Option/Except at narrow boundary points, (c) proof-obligation
  discharge extending `saw_unsafeAssert`. The right answer
  probably needs a small experiment per option on the 9
  regression-seed proofs.
- **Which docs to merge.** `soundness-boundaries.md` and
  `residual-trust.md` cover the same ground from different
  angles; `rearchitecting-plan.md` already schedules a merge.
  Whether to do that before or after the wrap decision is
  taste.
