# Phase 1a + 2 verification review
*2026-05-02*

## Methodology

Independent verification: read the actual source for each L-N item
(no reliance on commit messages or self-reports), located the
claimed regression test in `saw-core-lean/smoketest/SmokeTest.hs` or
under `intTests/test_lean_soundness_*/`, and ran each suite. The
saw-core-lean smoketest was run via `cabal test
saw-core-lean-smoketest` (all 34 cases pass). The integration suite
was run via `make -C otherTests/saw-core-lean test` (zero non-empty
diffs, zero elaboration failures). Three intTests were spot-checked
with `make -C intTests/test_lean_soundness_X test`
(`test_lean_soundness_natrec`, `..._fix_rejection`,
`..._polymorphic_nested`); two Lean-only intTests were run end-to-end
with `lake env lean` available (`..._unsafe_assert_prop`,
`..._coerce_shape`, plus `test_lean_walkthrough_proof`). Pretty-
printer claims were checked with `wc -l` and `awk` on the cited
`.lean.good`. The error-polish text and L-13 doc rewrites were read
directly. I did NOT attempt to construct a counter-example fuzz
input for `polymorphismResidual`, did not run the entire `intTests/`
suite, and did not rebuild the saw binary.

## Per-item verification

| Item | Code change present | Test pinning | Test passes | Notes |
|------|---------------------|--------------|-------------|-------|
| L-1  | Yes | Smoketest x3 + `intTests/test_lean_soundness_polymorphic{,_nested}` | Yes | Full-tree walk in `Exporter.hs:997-1042`; visits all subterms via `Foldable.traverse_ go tf`. |
| L-2  | Yes | `intTests/test_lean_soundness_unsafe_assert_prop/{attack,non_prop}.lean` | Yes (lake locally) | `unsafeAssert : (α : Type) → ...` in `SAWCorePrimitives.lean:274`. Attack rejected, non_prop accepted. |
| L-3  | Yes | Smoketest covers all 5 reacher types | Yes | `unsoundRecursorDatatypes = {Nat, Pos, Z, AccessibleNat, AccessiblePos}` at `Exporter.hs:833-834`. `leanOpaqueBuiltins` correctly demoted to ergonomic-only. |
| L-4  | Doc-only | N/A | N/A | `SAWCoreVectors.lean:9-46` and `2026-04-24_soundness-boundaries.md:102-117` document the analyzed residual. |
| L-5  | Yes | `intTests/test_lean_soundness_fix_rejection` | Yes | `UseReject` ctor in `SpecialTreatment.hs:124`; entries for `fix` / `fix_unfold` at lines 447, 456; `RejectedPrimitive` thrown in `Term.hs:302-304, 394-396`. |
| L-6  | Yes | Smoketest "scNormalize cap fails loud, never silent (L-6)" + "is set to 100 iterations" | Yes | `iterateNormalizeToFixedPoint` at `Exporter.hs:585-600` calls `fail` at cap. Mock-normaliser smoketest confirms throw. |
| L-7  | Yes | Smoketest "SAW ite/iteDep argument order preserved (L-7)" | Yes | Lean-side `iteDep p b fT fF = Bool.rec fF fT b` (permuted) in `SAWCorePreludeExtra.lean:42`; smoketest asserts `ite Bool Bool.true Bool.false Bool.true` substring. |
| L-8  | Yes | `intTests/test_lean_soundness_coerce_shape/{attack,positive}.lean` | Yes (lake locally) | Axiom shape `(α β : Type) → @Eq Type α β → α → β` at `SAWCorePrimitives.lean:250`. Attack at Type 1 rejected. |
| L-9  | Yes | Smoketest "applied constructor emits @-prefix at use site (L-9)" + 30 `@<DT>.rec` matches across `.lean.good` | Yes | `assertContains "@Either.Left"` covers ctor head; recursor head pinned indirectly via integration outputs. |
| L-10 | Yes | Smoketest x2 (Type, Prop) | Yes | sort 0 → `Type`, propSort → `Prop`. No `Type 1` / `Sort` drift. |
| L-11 | Yes | Smoketest x4 (alphanumeric, special chars, Lean reserved, distinct outputs) | Yes | `escapeIdent` covers reserved words (`match`, `do`, `for`, `where`, `instance`, `Type`, `Prop`) and Op_-prefix. |
| L-12 | Yes | Smoketest x3 (polymorphismResidual direct cases) | Partial | Code at `Exporter.hs:1135-1143` runs the gate per Cryptol def. **The L-12 intTest dir `intTests/test_lean_soundness_cryptol_module_gates/` is empty** — see Issues. |
| L-13 | Yes (doc) | Doc cites paths | N/A | `2026-04-24_soundness-boundaries.md` lines 42-53 etc. table-format with test paths. |
| L-14 | Yes | Smoketest "every Prelude primitive is mapped or intentional (L-14)" | Yes | `auditPreludePrimitivesForLean` at `Exporter.hs:687-713`; exception list at lines 736-799 with category comments. |
| L-15 | Yes | CI matrix includes both targets | Verified by reading `.github/workflows/ci.yml:199-206` | saw-core-lean-{smoketest,tests} listed in `cabal-collect-bins`; matrix runs them via `dist-tests/${{ matrix.suite }}` at line 777. |
| L-16 | Yes | Smoketest "Bool#rec doesn't surface bare in translated output (L-16)" | Yes | `iteDep, ite, iteDep_True, iteDep_False, ite_eq_iteDep` in `leanOpaqueBuiltins` at `Exporter.hs:973`. Zero `Bool.rec` matches in any `.lean.good`. |
| Walkthrough | Yes | `intTests/test_lean_walkthrough_proof/proof.lean` | Yes (lake locally) | proof.lean compiles; tactic discharges goal. Verbatim copy of `test_offline_lean.t2_prove0.lean.good` body (modulo whitespace). |
| @[simp] | Yes | rfl-proven in support library | Verified by reading | `iteDep_True`, `iteDep_False`, `ite_eq_iteDep`, `ite_True`, `ite_False` all `@[simp]` in `SAWCorePreludeExtra.lean:49-73`. |
| Error polish | Yes | Existing intTest log.goods (e.g. `nat_rec.log.good`, `poly_nested.log.good`) reflect the new text | Yes | `ppTranslationError` in `Monad.hs:71-127` has "What this means", "Likely causes", "Workarounds" structure for `UnsoundRecursor` and `RejectedPrimitive`. `polymorphismResidual` polished separately at `Exporter.hs:1021-1042`. |
| Pretty-printer | Yes | `wc -l = 179`, max line = 81 cols on `test_cryptol_module_simple.module.lean.good` | Yes | `Pretty.hs:166-179` uses `group $ fillSep`, no `hang 2`. Comment cites Audit C / Phase 2. |

## L-16 deep-dive

The L-16 fix is correct. Walking the chain:

1. **Cryptol `if c then x else y`** lowers (via Cryptol→SAWCore) to
   a `Prelude.ite Bool c x y` application — argument shape
   `(motive_or_ty, scrutinee, trueBranch, falseBranch)`.

2. **`scNormalizeForLean`** receives the term and calls
   `scNormalize sc unfold`, where `unfold` returns `False` for
   names whose VarIndex is in the `opaqueSet`. The opaqueSet
   includes `Set.fromList builtinIdxs` from `leanOpaqueBuiltins`,
   which post-L-16 contains `"ite", "iteDep", "iteDep_True",
   "iteDep_False", "ite_eq_iteDep"`
   (`Exporter.hs:959-973`). So `Prelude.ite` is NOT unfolded.
   The surface stays at `Prelude.ite`.

3. **Translator emits via SpecialTreatment.** `SpecialTreatment.hs:364`
   maps `"ite"` to `mapsTo sawCorePreludeExtraModule "ite"`. The
   emitted Lean head is therefore
   `CryptolToLean.SAWCorePreludeExtra.ite`, with the SAW argument
   list preserved positionally: `(α, b, x, y)` where `x` is the
   true-branch and `y` is the false-branch.

4. **Lean-side `ite` realises the permutation.** From
   `SAWCorePreludeExtra.lean:58-59`:
   ```lean
   def ite.{u} (a : Sort u) (b : Bool) (x y : a) : a :=
     Bool.rec y x b
   ```
   Lean's auto-generated `Bool.rec` is
   `(motive : Bool → Sort u) → motive false → motive true → (b : Bool)
   → motive b` (False-first). The body passes `y` as Lean's
   `false-case` and `x` as Lean's `true-case`. So when SAW says
   `x` is the true-branch and `y` is the false-branch, Lean
   correctly returns `x` when `b = true` and `y` when `b = false`.
   `iteDep` does the same with `Bool.rec fF fT b`
   (line 42), checked by `iteDep_True`/`iteDep_False` at `rfl`.

5. **No bare `@Bool.rec` leak.** Pre-L-16 the wrappers were not
   opaque, so `scNormalize` would step through them into their
   underlying `Bool#rec1` and the translator would emit `@Bool.rec`
   in SAW order — silently swapping branches. Post-L-16, opacity
   stops normalization at the wrapper level. The smoketest pins
   this with `assertNotContains "Bool.rec"` on a translated `ite`
   call. A regression that drops one of the five names from
   `leanOpaqueBuiltins` would re-open the bug; the smoketest
   would catch it.

The fix is sound. The only remaining gap is the case where a user
hand-builds a term containing a literal `Bool#rec` via `parse_core`
(i.e. doesn't go through `ite`/`iteDep` at all). That gap is
documented in `2026-04-24_soundness-boundaries.md` and is not in
scope for the L-16 fix.

One subtle point worth checking: if a primitive *other than the
five wrappers* uses `Bool#rec1` in its body and is unfolded by
scNormalize, the translator could still emit a bare `@Bool.rec`
swapped at the call site. Spot-checking `not`, `and`, `or`, `xor`,
`boolEq`: a comment in `leanOpaqueBuiltins` (lines 974-978) claims
they reduce one step to `ite` and stop there because `ite` is
opaque. The chain is plausible (those defs are typically `\b1 b2 ->
ite Bool b1 b2 ...`) but I did not independently verify each by
inspecting the Prelude source. The integration tests (which would
diff if any of these emitted `Bool.rec`) cover this in practice —
no `.lean.good` contains `Bool.rec`. Still, the comment-as-
guarantee here is the kind of thing the post-audit plan expressly
warns about (cross-cutting finding #1: "no comment-grade
guarantees"). A targeted smoketest on `not (ite ...)` etc. would
upgrade this to test-grade.

## Issues found

- **[Severity: low] Empty intTest dir `intTests/test_lean_soundness_cryptol_module_gates/`.**
  The directory exists on disk but has no files and is not tracked
  by git. Likely a leftover from creating an L-12 intTest that was
  abandoned in favor of smoketest-level pinning. Cleanup: `rmdir
  intTests/test_lean_soundness_cryptol_module_gates`.

- **[Severity: low] L-12 has no end-to-end intTest.** The L-12
  Haskell-level gate (the `Foldable.forM_` over `tm` in
  `writeLeanCryptolModule`) is exercised only indirectly by the
  three `polymorphismResidual` smoketests. There is no
  intTest-level proof that a `.cry` file with a universe-polymorphic
  def is actually rejected by `write_lean_cryptol_module`. The
  L-15 commit message acknowledges this ("L-12 is documentation-only",
  which is incorrect — there's real Haskell code at lines 1135-1143
  of `Exporter.hs`). Recommended: add a tiny `.cry` test that
  defines a universe-polymorphic value and confirm SAW exits with
  the polymorphismResidual diagnostic. The empty test dir suggests
  this was started and dropped.

- **[Severity: low] Post-audit plan doc lists L-1..L-15 only.**
  `saw-core-lean/doc/2026-05-02_post-audit-plan.md` does not
  mention L-16 anywhere. The lockdown-was-supposed-to-close-it
  framing isn't covered. The doc should either:
  (a) gain a §"Mid-flight additions: L-16" subsection, or
  (b) mark itself as superseded by an updated plan that includes
  L-16. Otherwise a future contributor reading the plan would
  conclude "Phase 1a closed at L-15" and miss the most consequential
  finding.

- **[Severity: low] L-16 mitigation relies on a comment-grade
  argument for `not`/`and`/`or`/`xor`/`boolEq`.** See L-16 deep-dive
  above. Add a smoketest that emits one of these on a variable
  Bool argument and asserts no `Bool.rec` in the output. (The
  existing L-16 smoketest only covers the bare `ite` shape.)

- **[Severity: low] L-15 commit message contains a factual
  inaccuracy.** It states "L-4, L-12, L-13 are documentation-only";
  L-12 is not documentation-only (real `Foldable.forM_` gate code
  in `Exporter.hs`). Doesn't affect runtime behavior; harmless.

- **[Severity: low] The walkthrough doc and proof.lean are
  consistent on the goal shape, but the proof.lean is hardcoded —
  if `test_offline_lean.t2_prove0.lean.good` ever changes (e.g.
  because the simp lemmas trigger a different pretty-printing
  route), `proof.lean` won't auto-update.** Consider regenerating
  proof.lean from the `.lean.good` as part of the test, or making
  the test diff the two. Not urgent — both files are ~30 lines and
  drift would be obvious.

## Things working as claimed

- **All 34 saw-core-lean-smoketest cases pass** (`cabal test
  saw-core-lean-smoketest`). Each lockdown item that claims smoketest
  pinning is in fact pinned in `SmokeTest.hs` and the test asserts
  what the lockdown claims.
- **Integration suite is clean.** All 15 `.saw` drivers under
  `otherTests/saw-core-lean/` complete with empty `.diff` files.
  No `.lean.elaboration.fail` files generated by the on-by-default
  `lean-elaborate` flag.
- **The two Lean-only intTests run cleanly** when `lake` is on
  PATH: `unsafe_assert_prop` rejects the universe attacks AND
  accepts the translator-emitted shapes;
  `test_lean_soundness_coerce_shape` rejects the Type-1 attack.
  The walkthrough proof discharges the goal end-to-end.
- **L-16 is a clean fix.** The chain `Cryptol if → ite → opaque →
  SAWCorePreludeExtra.ite (permuted Bool.rec)` works correctly,
  and zero `Bool.rec` matches anywhere in the integration
  `.lean.good` corpus confirms post-L-16 hygiene.
- **Pretty-printer numbers are exact.** 179 lines, max line length
  81 columns on `test_cryptol_module_simple.module.lean.good`.
  The output is genuinely readable, not just compact (multi-arg
  function applications wrap at arg boundaries via `fillSep`,
  not at character boundaries).
- **L-13 doc rewrite is real.** The soundness-boundaries doc cites
  `intTests/test_lean_soundness_*/` paths in a table format for
  every refusal case, and pins the residual-trust list (Vec/Vector
  iso, Bool#rec direct surface) with explicit "documented residual"
  framing.
- **Error-polish reaches the ground truth.** `nat_rec.log.good`
  and `poly_nested.log.good` both contain "What this means for
  your Cryptol code" / "Likely causes" / "Workarounds" sections.
- **CI integration is correct.** `cabal-test-suites` includes
  both Lean-related stanzas; the `cabal-test` matrix step runs
  `dist-tests/${{ matrix.suite }}` for each, which is the binary
  produced by `cabal-collect-bins`.
- **Auto-derive is doing real work.** `discoverNatRecReachers` walks
  the module map and detects defs whose body contains a recursor
  over any of the 5 unsound types; `leanOpaqueBuiltins` is reduced
  to ergonomic clean-surface entries, with comments documenting
  each entry's purpose.
- **No tracked runtime artifacts.** All test dirs that produce
  `.log` / `.diff` / `.rawlog` files have a `.gitignore`; runtime
  artifacts are correctly untracked. Repo `git status -s` shows
  only the three submodules in pre-existing modified state plus
  one untracked investigation note.

## Recommendations

**Must-fix before Phase 3:**

1. Either add an actual `intTests/test_lean_soundness_cryptol_module_gates/`
   end-to-end test or remove the empty directory. The current state
   (empty dir + claim that the gate is pinned at the smoketest level)
   is fine but slightly misleading.

2. Update `2026-05-02_post-audit-plan.md` to include L-16 in the
   lockdown catalog, or supersede that doc with a current one. The
   highest-impact finding of the entire phase isn't documented in
   the plan.

**Nice-to-have:**

3. Add a smoketest case for the `not`/`and`/`or`/`xor`/`boolEq` →
   `ite` reduction, asserting no `Bool.rec` in the output. Closes
   the only L-16 gap that's currently a comment-grade guarantee.

4. Consider a positive smoketest for `writeLeanCryptolModule`'s
   gate that doesn't require a `.cry` file (mock the module map),
   so L-12 has a smoketest that exercises the actual code path
   rather than the helper function.

5. Wire `lake env lean` into the L-15 CI step (or a follow-on step)
   so the `_unsafe_assert_prop` / `_coerce_shape` /
   `_walkthrough_proof` Lean-only tests run in CI rather than
   skip-cleanly. They currently skip when `lake` isn't on PATH —
   acceptable today but a real CI run with `lake` would catch
   regressions earlier.

6. The `leanIntentionallyUnmappedPrimitives` exception list (~75
   names) is the kind of hand-maintained list the lockdown
   principle pushes against. L-14 catches NEW omissions but doesn't
   catch a name moved from "mapped" to "intentionally unmapped"
   without good reason. A periodic audit (or a per-category cap)
   would tighten this further. Low priority.

Phase 1a + 2 is in good shape. The actual delivered work matches
the claims with a few small process gaps (empty test dir, plan doc
behind, L-16 not in the catalog). No soundness regressions found.
The pretty-printer change is genuinely useful — output went from
"unreadable" to "readable" by direct inspection, not just by
column count. The walkthrough proof actually closes the goal.
