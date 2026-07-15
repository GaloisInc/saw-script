# Release 0.01 comprehensive audit — drift & removal candidates

**Date**: 2026-07-14. **Status**: FINDINGS FOR DISCUSSION — nothing
here has been removed or changed; every item awaits explicit sign-off
(user instruction: "don't kill anything until we've discussed it").

**Method**: four independent read-only audit passes (Haskell source +
smoketest; Lean support library cross-referenced against the emitter's
identifier strings, all 296 `*.lean.good` goldens, and 36 live
`proof.lean` consumers; documentation vs code reality; deep test/
support tree ghost-hunt across the three design eras). Evidence for
every claim is file:line plus caller/consumer grep counts, recorded in
the per-pass reports (session scratch; load-bearing citations
reproduced here).

**Headline**: the tree is fundamentally sound. **No retired-era
identifier survives in any emitted golden or live proof source** —
the fossils are confined to prose (comments, headers, GAP notes), a
handful of genuinely dead code islands the anti-regression lint
couldn't see, and gitignored litter. Two findings are user-facing
enough to fix before release regardless of the removal discussion
(§A1, §A2).

---

## A. Misleading-for-users docs (fix before release; pure doc edits)

1. **`doc/proof-cookbook.md` teaches tactics that do not exist.**
   Lines 17, 24, 30–33, 210–227, 256 describe `saw_bv`, `saw_unfold`,
   `saw_to_bitvec` from a `CryptolToLean.Tactics` module — no such
   module or macros exist anywhere in the support library. A user
   following the cookbook hits "unknown tactic". (The cookbook's named
   *lemmas* all resolve.) Also line 208 cites a nonexistent
   `proofs/cookbook/` test. Fix: delete the tactic material (or build
   the module — 0.02 ergonomics).
2. **"Current plan-of-record" links are broken and stale.**
   `README.md:70-74`, `architecture.md:94,191`,
   `getting-started.md:227`, `contributing.md:147,216` point at
   `doc/2026-05-05_long-term-plan.md`, which lives only in
   `doc/archive/` and is superseded by
   `doc/2026-07-14_release-plan.md`. Also `README.md:76` +
   `architecture.md:95,201` reference a nonexistent `doc/audit/`
   directory (file is in `doc/archive/`).
3. **`README.md:40-43` "bv* operations as axioms" is false** — all 41
   `bv*` ops are `noncomputable def`s over native `BitVec`; `gen` and
   `atWithDefault` are structural defs. The only true residual is
   that the `bitvector` *type* is `Vec n Bool`. Same confusion in
   `architecture.md:206-209` and `SAWCoreBitvectors.lean:5-23`
   (frames the BitVec binding as future work that already happened).
4. **`getting-started.md:192-199` "`error` is still axiomatic"**
   predates the 2026-07-14 raw-error disposition (`error` is
   `mapsToWrapped saw_throw_error`; raw positions reject).
5. **Support-library header/comment drift**:
   `SAWCoreBitvectors_proofs.lean:19-32` and
   `SAWCorePrelude_proofs.lean:15-18` claim lemmas "are still
   axiomatic" — both files now contain ZERO axioms (every lemma
   proven). `SAWCorePrimitives.lean:1013-1039` says `error` maps to
   `reject`/"fails loud at translation", contradicting the correct
   section right below it (1041-1056); 1069-1073 cites deleted
   `error_unrestricted`; 115-121 justifies Inhabited instances via
   deleted `error.{u}`. `SAWCorePrelude_proofs.lean:752` cites
   `saw_self_ref_comp_iterate`, which exists only in design docs.
6. **Demo README stub-name typo**: `saw-lean-example/README.md:41,77`
   show `theorem goal : <Prop> := by sorry`; the actual emission is
   `def goal : Prop := …` + `theorem goal_holds : goal := by sorry`.

## B. Guard gap (an ADD, not a removal — high value, tiny change)

- `support/lean-driver-test.sh:116`: the obsolete-helper scan that
  keeps era-1 names out of emitted Lean omits four of them:
  `rawifyExceptToRaw`, `divNatChecked`, `modNatChecked`,
  `BoundedVecFold`. Extend the alternation. (This guard is why the
  goldens are fossil-free — worth completing.)

## C. Dead-code removal candidates (Haskell) — for discussion

High confidence (zero callers/producers, evidence in report):
1. `Term.hs:352-353` `_gammaFieldsPendingUse` + the write-only
   `BindingInfo` fields `biSourceType`/`biLeanType` (:342/:344) — the
   promised Slice-2/5 consumer never landed; the `_` prefix hid it
   from warnings.
2. `Term.hs:123` `RawLeanFormalPosition` (`RawReason` arm) — zero
   producers/consumers; the other four arms are live.

Needs verification (data-model surface; want sign-off + a
build/corpus check):
3. `Term.hs:300/337` `ttProducedAt`/`biBoundPosition` — a closed
   write-only loop; the live position mechanism is the threaded
   parameter in `translateSharedAt:5595`, and even the trace reads
   only `ttShape`. Remove the stored fields + plumbing, or correct
   the three docstrings that promise they become "the authority".
4. `Monad.hs:44-69` — five `TranslationError` constructors never
   thrown (`NotSupported`, `NotExpr`, `NotType`, `BadTerm`,
   `CannotCreateDefaultValue`); all live rejection flows use
   `RejectedPrimitive` (80 sites) / `UnsoundRecursor` /
   `ForbiddenAdaptation`. Delete or mark Rocq-parity-unreachable.
5. `Term.hs:207-208` `ResultMode` arms `RawResult`/`FunctionResult` —
   every producer emits `RuntimeResult`; two dead case arms. Collapse
   or mark reserved.

Doc-only in source: `ExpectFunctionPosition` "transitional bridge"
(:131-134) and `FunctionWithNatLtArg` "folds into FunctionArg"
(:186-190) describe merges that never happened — both are permanent
conventions now; ~60 "legacy path" narration comments describe THE
path (the legacy alternative was deleted); locals
`legacyWrap`/`legacyBinderWrap` (:1113/:1125) are misnomers. Keep the
tombstone NOTEs — the smoketest lint depends on them.

Export hygiene (low risk): unused-external exports in `Term.hs`
(`translateTermLet`, `translateAt`, `ExpectedPosition`, `RawReason`,
`TranslatedTerm`) and `SpecialTreatment.hs` (9 names). Mechanical
backstop for all of §C: one `-Wall -Wunused-imports
-Wunused-top-binds` build.

## D. Dead-code removal candidates (Lean support library)

Tier 1 — emitter-confirmed safe-delete (the `partialOpContracts`
table routes exclusively to the `_checkedM` forms; `Term.hs:2085-2104`):
the eight pure `_checked` variants `bvUDiv_checked`, `bvURem_checked`,
`bvSDiv_checked`, `bvSRem_checked`, `intDiv_checked`, `intMod_checked`,
`ratio_checked`, `rationalRecip_checked` (the three Nat `_checked`
forms stay — they ARE the emitted forms).

Tier 2 — plain (non-simp) theorems with zero consumers across
emitter/goldens/proofs: 4 `isBv*_def` `Iff.rfl` restatements;
`eq_imp_bvEq_eq_true`; `vecToBitVec_bvNat`; `bvEq_eq_BitVec_beq`;
5 `atWithDefault_*` lemmas subsumed by `@[simp] atWithDefault_lt`;
5 unused `atWithDefaultM_*` congruence forms;
`ecSDiv/ecSMod_checkedM_TCNum_succ`; `atInBounds` (docstring falsely
claims the backend emits it); `atRuntimeCheckedM_eq_checked`.

Tier 3 — `@[simp]` members with zero visible consumers (grep cannot
prove simp-set deadness; verify by building the proof corpus without
them): the entire 16-wide literal-peeler family
`atWithDefault_16_lit_0..15` (the 4-wide analog IS used by the
salsa20 proof); 4 `vecToBitVec_bv*` bridges; 9 Nat-alias simp lemmas;
`iteM_pure_*`/`iteM_error`/`sawLet_ok`/`sawLet_error`/`coerce_id`/
`ofFnM_except_ok`.

Tier 4 — the 8 `Inhabited` instances (`SAWCorePrimitives.lean:123-149`):
both original rationales are gone (`error.{u}` deleted; the emitter no
longer injects `[Inhabited]` binders — `Term.hs:659-672`, `5322-5330`).
Instance resolution is grep-invisible: remove + full rebuild to verify.

**Explicitly parked, do NOT remove**: `foldl_eq_natRec_atWithDefault`
(documented OP-3 bridge infrastructure; its partner
`foldr_and_gen_eq_true_of_all` is live in three ChaCha20 proofs), and
`saw_fix_unique_exists` (the documented 0.01 limitation, OP-3 scope).

## E. Corpus prose fossils (doc-only edits)

- `drivers/offline_lean_e_series/….saw:83` "BoundedVecFold lowering
  (Phase 5 Slice B)" — era-1 names in a live comment.
- `drivers/cryptol_module_salsa20_q/….saw:1,3` — era-1 phase
  numbering.
- `proof-gaps/cryptol_chacha20_core_iterate/GAP.md:18-24` — the
  "2026-07-03 probe" paragraph documents an artifact that no longer
  exists and is the tree's sole surviving `divNatChecked`/
  `modNatChecked` mention.
- `saw-boundary/fix_unfold_rejection/.known-gap` — says the rejection
  "pins missing proof-carrying emission", but proof-carrying fix
  emission now exists; the rejection is still right (primitive proof
  principle), the wording isn't.
- Five differential `.known-gap` reasons say ops are defined "through
  runtime error" where SAW actually fails `Unimplemented:` (simulator)
  — low-stakes precision fix.
- `saw.cabal:1165-1167` — suite description predates the full matrix.
- "Phase-beta" vocabulary in 6 test comments — concept current, name
  era-2; team call whether to rename to "value-domain convention".

## F. Gitignored litter (invisible to a clean checkout; safe-delete)

- `lean/intTestsProbe/` — ~35 May-era hand-probe files + two scratch
  dirs (the directory itself is the live staging root — delete the
  stale files only).
- `lean/demoProbe/{eq,invol}/` — staging copies, regenerated.
- `.snapshots/slice0-baseline`, `.snapshots/op1-baseline` — superseded
  by `op2-baseline`.
- `saw-lean-example/proof/{eq,invol}/Emitted.olean` — stale May
  oleans; the Makefile's own `clean` already lists them.
- Repo-root `.tmp/pr-body.md` (May) + `.tmp/difftest-goal.md` (June).

## G. Structural discussion items (not defects)

- `lean-reverse-example/` — standalone April Lean project, no SAW
  involvement; conceptual ancestor of the demo's specRev/implRev
  naming, referenced only by comments in the two `rev.cry` files.
  Keep as documented motivation or retire.
- Archive candidate: `doc/2026-07-08_position-directed-translation-plan.md`
  (all 8 slices complete; TODO no longer lists it active). Keep
  top-level: the calculus doc (canonical contract), the
  obligation-placement design (OP-3 open), the OP-3 refuted-candidate
  record.
- Test-gap list (KEEP the code; add coverage): 11 emitter-wired
  support-library helpers with zero golden/proof coverage
  (`genWithProof_checkedM` family, `if0NatRaw`/`if0NatM`/`natCaseRaw`,
  `saw_fix_unique_exists_raw`/`saw_fix_choose_raw`,
  `mkFloat`/`mkDouble`).
- Self-test gap: `atRuntimeCheckedM` and `saw_throw_error` have golden
  coverage but no in-library `#guard_msgs` fences (the
  `saw_ctor_order` pattern).

## Verified healthy (coverage statement)

Exactly two axioms in the TCB (the Vec/BitVec round-trip pair), zero
axioms in both `_proofs` files; no fully-dead top-level function among
Term.hs's 199 bindings beyond the items above; all reader/state fields
and all other enum arms live; the smoketest anti-regression lint
current and self-verifying; every deleted-machinery name either absent
or a deliberate tombstone/guard; `@Eq.rec` heads everywhere (no
`Eq__rec` output fossil); harness verbs/env-vars all consumed;
`.known-gap` corpus accurate apart from the wording items above;
offline_lean rows fully emission-only-coherent; the Rocq example tree
is an intentional frozen mirror; census 64 == disk == STATUS.
