# P6 investigation: Prop/Type cumulativity gap

*Agent report — 2026-04-22*

Follow-up to `2026-04-22_p4-v2-status.md`. Validates (and refines) the
preliminary PLift-insertion sketch against concrete Lean probes. Headline:
**PLift insertion is not the right fix; universe-polymorphizing the
sort-0 inductives is.**

## 0. TL;DR

- Of 99 reported `lake env lean` errors, only **17 are actually the
  Prop/Type gap** (Q1). The other 82 are two independent issues that
  must not be conflated with this investigation:
  - **68** are a `Nat` vs `_root_.Nat` name-resolution bug in
    scaffolding (`SAWCoreVectors.Vec` expects Lean's native `Nat` but
    the prelude defines a separate local `Nat` inductive).
  - **13** are the Lean reserved keyword `at` — `Prelude.at` needs
    escaping/quoting on emission.
- The 17 Prop/Type errors all fire on three sort-0 inductives:
  `Either`, `Maybe`, `PairType`. They're emitted monomorphically at
  `Type`, but SAWCore uses them with `Prop`-valued arguments via
  cumulativity.
- **Winning approach: Approach C (universe-polymorphization).**
  - Emit sort-0 inductives as `Foo.{u, v} (x : Sort u) (y : Sort v) :
    Sort (max 1 (max u v))` — the pattern P4 v2 already applies to
    sort-1 inductives (e.g., `PairType1`). Extend to sort-0.
  - For `def`s with sort-0 binders, emit a **single** shared universe
    variable spanning all sort-0 binders (not per-binder fresh), to
    preserve SAWCore's "all these binders are at the same sort"
    semantics that the original sources rely on (e.g., `coerce__def
    : (a b : sort 0) -> Eq (sort 0) a b -> ...`).
  - **Zero PLift wrapping.** No Coe tricks. No support-lib additions.
- All 17 Prop/Type errors resolve with this approach; probed on
  `natCompareLe`, `proveEqNat`, and `eitherCong0`.
- Effort: **0.5–1 day**. Smaller than the preliminary 1-day estimate
  because it builds on P4 v2's existing `SortMax1Vars` machinery.

Confidence key:
- **Certain (probed)**: C in this doc = Approach C works on a verbatim
  copy of the generated `proveEqNat` body with polymorphic `Maybe`.
- **Certain (probed)**: PLift-based Approach A needs downstream
  rewriting (pattern-match sites must unwrap); CoeSort-based Approach B
  works for inferred type args but not for explicit `@Foo (P : Prop)`.
- **Reasoned**: "defs need single shared universe for sort-0 binders"
  is reasoned from the `coerce__def` case + a small probe; I've not
  exhaustively re-run the whole SAWCorePrelude under the proposed
  translator change.

## 1. What's actually failing (Q1)

Fresh reproduction run. 99 error lines after P4 v2. Breakdown:

| Kind | Count | Example |
|---|---|---|
| `Application type mismatch` with sort-1 expectation but Prop arg | 17 | `Either (IsLtNat m n)` |
| `Application type mismatch` with `_root_.Nat` expectation but local `Nat` | 68 | `SAWCoreVectors.Vec n` |
| `unexpected token 'at'` | 13 | `noncomputable def at ...` |
| `maxErrors reached` | 1 | — |

**Only the first group is the Prop/Type issue.** The taxonomy:

### 1a. The 17 genuine Prop/Type errors

All fire on calls to `Either`, `Maybe`, or `@Maybe.Left`/`@Maybe.Just`/
`@Maybe.Nothing` with a Prop-valued type argument. Sites:

- `natCompareLe` (axiom signature)
- `proveEqNat` (body — `Maybe (m = n)`, `@Maybe.Just (@Eq Nat Zero
  Zero) _`, several `@Maybe.Nothing` uses, one `maybe (@Eq Nat m n)
  ...`)
- `proveLeNat`, `proveLtNat` (signatures — `Maybe (IsLeNat x y)`)
- A few nested `Maybe (IsLtNat ...)` / `Maybe (Succ m = n)`.

The root: SAWCore `Either (s t : sort 0) : sort 0` and `Maybe (a : sort
0) : sort 0`. Callers pass `Prop`-valued args (`IsLtNat`, `IsLeNat`,
`Eq Nat …`) via SAWCore cumulativity (`Prop ⊂ sort 0`). Lean is
non-cumulative, so the Prop args refuse to elaborate at the `Type`
binder position.

### 1b. The 68 `Nat` vs `_root_.Nat` errors (SEPARATE ISSUE — OUT OF SCOPE)

`SAWCorePrelude.lean` defines `inductive Nat : Type where | Zero |
NatPos : Pos -> Nat` — a module-local type distinct from Lean's
`_root_.Nat`. Fine in isolation. The bug: `CryptolToLean.SAWCoreVectors`
has

```lean
abbrev Vec (n : Nat) (α : Type) : Type := Vector α n
```

where `Nat` resolves to `_root_.Nat` (the scaffolding doesn't import
the prelude — it can't, since the prelude imports *it*). When
downstream defs in `SAWCorePrelude.lean` write `Vec n a` and `n : Nat`
(local), Lean rejects: local `Nat` ≠ `_root_.Nat`.

This is a **scaffolding-layer bug**, not a translator bug. Deserves
its own follow-up. The fix is either:
(a) re-map SAWCore's `Nat` to Lean's native `Nat` via `mapsToCore`
    (currently explicitly rejected by SpecialTreatment.hs lines
    247-251 on soundness grounds — the binary-positive vs unary
    encoding is genuinely different), or
(b) make `SAWCoreVectors.Vec` take the local `Nat`, requiring a
    cyclic-import-breaking refactor.

### 1c. The 13 `at` keyword errors (SEPARATE ISSUE — OUT OF SCOPE)

SAWCore's `Prelude.at` translates to Lean `noncomputable def at
(...)`. `at` is a reserved keyword in Lean 4 (used in tactics like
`rw [h] at foo`). The translator needs to escape it:
either rename (e.g., `at_` or `at'`) via SpecialTreatment, or
always emit reserved identifiers as `«at»`.

This is a **mechanical translator bug**, trivially fixable, unrelated
to universe issues.

### 1d. Walkthrough of 3 representative failing defs

**`natCompareLe`** — axiom. SAWCore source:

```
primitive natCompareLe : (m n : Nat) -> Either (IsLtNat m n) (IsLeNat n m);
```

Emitted (line 2001):

```lean
axiom natCompareLe : (m : Nat) -> (n : Nat) -> Either (IsLtNat m n) (IsLeNat n m)
```

Fails because `IsLtNat m n : Prop` but `Either` expects `Type`.

What we should emit: nothing different at the use site. We should
emit `Either` *itself* as universe-polymorphic so that at call
site, `@Either.{0, 0}` resolves the arg-universes to 0 (the sort of
Prop).

**`proveEqNat`** — def with body. SAWCore source:

```
proveEqNat : (m n : Nat) -> Maybe (Eq Nat m n);
proveEqNat = ... Nat__rec ... Maybe.Just ... Maybe.Nothing ... maybe ...
```

Emitted: 75-line nested Nat__rec with `@Maybe.Just (@Eq Nat 0 0) ...`,
`@Maybe.Nothing (@Eq Nat …) `, and `maybe (@Eq Nat m n) ...`. Every
`Maybe (Eq …)` fails because `@Eq Nat m n : Prop` is passed to
`Maybe : Type -> Type`.

What we should emit: same body. Just polymorphize `Maybe` and `maybe`
(the eliminator-like def, not the type).

**`proveLeNat` / `proveLtNat`** — axiom / def with `Maybe (IsLeNat x
y)`. Same pattern.

## 2. Approaches considered, probed

Four candidate approaches. Ran probe `.lean` files in
`/tmp/p6_probes/` (saved to `.tmp/p6_probes/` because sandbox
can't write `/tmp`).

### Approach A: Manual PLift wrapping at the generator

Translator detects Prop args at Type positions, emits `@PLift (Arg)`
+ `@PLift.up (value)` on construction, `_.down` on destruction.

**Probed result**: works for isolated cases (A_manual_plift.lean,
A_soundness_check.lean). Rejected for three reasons:

1. **Large translator surface area**. Requires threading expected-type
   information through `translateTerm`, because "this arg is at a
   Type position" depends on `scTypeOf(f)`, requiring a type-checker
   pass at translation time. Current translator is syntax-directed.

2. **Breaks downstream uses**. Any def that pattern-matches on
   `Either (PLift P) (PLift Q)` gets payloads `PLift P`, not `P`. A
   downstream SAWCore def that binds the proof and passes it where
   `P` is expected needs translator-inserted `.down` — another
   pass that needs to know when to unwrap.

3. **Ugly surface form**. Users reading the Lean output see
   `Maybe (PLift (m = n))` instead of `Maybe (m = n)`. Proof
   obligations get `PLift` noise.

### Approach B: CoeSort + CoeHead + Coe instance in the support lib

Install

```lean
instance : CoeSort Prop Type where coe p := PLift p
instance {P : Prop} : CoeHead P (PLift P) where coe p := PLift.up p
instance {P : Prop} : Coe (PLift P) P where coe p := p.down
```

in `SAWCorePreludeExtra.lean`. Lean's elaborator auto-inserts PLift
at Prop-in-Type sites.

**Probed result**: works for *inferred* type arguments (B3_coe_full.lean),
**and** works when the explicit `@foo (P : Prop)` type is definitionally
equal to the expected Prop — e.g. `@Maybe.Just (Nat.succ m = Nat.succ n)
(eqNatSucc m n e)` elaborates because `eqNatSucc`'s result type
`m.succ = n.succ` reduces to the expected type without needing PLift
(B_final_verify2.lean). However, when the expected type contains an
opaque `def` — e.g. `Succ m = Succ n` where `def Succ := Nat.succ`
blocks reduction — PLift *is* required, and CoeSort doesn't fire on
@-form type args (B_verify3.lean, B_debug_coe2.lean, B_debug_coe4.lean):

```
error: Application type mismatch: The argument
  eqNatSucc m n e
has type
  m.succ = n.succ
of sort `Prop` but is expected to have type
  PLift (Succ m = Succ n)
  ...
```

The generated prelude uses opaque defs like `Succ` (SAWCore's
successor, distinct from `Nat.succ` because the local `Nat` isn't
native Lean's), so the failure is not hypothetical — the real body
of `proveEqNat` hits it (B_proveEqNat_full.lean).

**Conclusion**: Rejected. Partial coverage isn't good enough; the
translator generates `Succ`-style opaque defs that would need
post-hoc unfolding or translator-side PLift insertion to rescue.
Approach C avoids both.

### Approach C: Universe-polymorphize sort-0 inductives (WINNER)

Match P4 v2's existing treatment of sort-1 inductives (like
`PairType1`). Emit:

```lean
inductive Either.{u, v} (s : Sort u) (t : Sort v) : Sort (max 1 (max u v)) where
  ...

inductive Maybe.{u} (a : Sort u) : Sort (max 1 u) where
  ...
```

At a use site with Prop args, Lean resolves `Either.{0, 0}` — no
translator-side logic needed. Result type is `Sort (max 1 (max 0
0)) = Sort 1 = Type 0`, matching SAWCore's `sort 0` semantics.

**Probed result**: works end-to-end on a verbatim copy of
`proveEqNat`'s body (`C_proveEqNat_full.lean`). Zero errors. Output
signature is exactly `(m n : Nat) → Maybe (m = n)` — no PLift noise,
matches SAWCore surface form.

One subtlety: `def`s (not inductives) with multiple sort-0 binders
using `Eq` between them (e.g. `coerce__def : (a b : sort 0) -> Eq
(sort 0) a b -> ...`) **must share a single universe variable**
across their sort-0 binders, else Lean fails to unify the Eq's
implicit type arg (probed: `C10b_full_poly_defs.lean` fails when
`x : Sort u2, y : Sort u3` are separate; `C_final2.lean` works
when all sort-0 binders share `u`).

Refined rule:

- **Inductive `data Foo (xs : sort 0) ... : sort 0`** → per-binder
  fresh universe, result sort `Sort (max 1 (max u1 u2 ...))`.
  Matches P4 v2's sort-1 treatment.
- **Def `foo : (xs : sort 0) -> ... -> sort 0`** → one fresh
  universe variable `u` shared across all sort-0 binders. Preserves
  SAWCore's "these binders are at the same sort" constraint that
  code like `coerce__def` implicitly relies on.

The shared-universe rule for defs is the minimal concession to Lean's
non-cumulativity. It's sound: SAWCore's source is well-typed
under any sort-0 instantiation including `Prop`; sharing a single
universe in Lean preserves that.

### Approach D: SpecialTreatment handwritten realizations for Either/Maybe

Replace `Either`, `Maybe`, `PairType` with handwritten
universe-polymorphic versions in `SAWCorePreludeExtra.lean`,
routed via SpecialTreatment `mapsTo`.

**Not probed** (would duplicate Approach C's work). Cheaper than
C in that it doesn't touch the translator, more expensive in that
it moves auto-generated inductives into the support library. If
C's translator changes prove risky, D is the fallback.

Soundness is equivalent to C. **Ergonomics: slightly worse** (users
see a jump between auto-translated vs handwritten names in the
generated file).

## 3. Translator changes required

### 3a. `SAWCoreLean.Term.translateBinder'` — emit a fresh universe for sort-0 binders

Currently `translateBinder'` calls `translateTerm ty` for the
binder's type. For `ty = Sort 0` this hits `translateSort`, which
returns `Lean.Type` — the monomorphic target.

Add a binder-context-aware path. Draft:

```haskell
translateBinder' vn ty f = do
  ty' <- translateBinderType ty  -- NEW: binder-aware sort translation
  ...

-- NEW function:
translateBinderType :: TermTranslationMonad m => Term -> m Lean.Term
translateBinderType ty = case unwrapTermF ty of
  FTermF (Sort s _)
    | s == propSort -> pure (Lean.Sort Lean.Prop)
    | otherwise     -> do
        uname <- freshUniverseName -- or shared, see below
        modify (over universeVars (Set.insert uname))
        pure (Lean.Sort (Lean.SortVar uname))
  _ -> translateTerm ty
```

Key subtlety: for defs (not inductives), all `sort 0` binders in one
def should share a universe. For inductives, they're per-binder
fresh. This context is already tracked: `translateDataType` in
`SAWModule.hs` uses `translateParams` separately; `translateDefBody`
uses it separately. We can distinguish by adding a flag to
`TranslationState` or passing a parameter.

Pragmatic approach: add a field `sort0UniverseMode :: Sort0Mode`
to the `TranslationState` (or a reader field), with two values
`PerBinder` (inductives) and `SharedPerDef` (defs). Each top-level
entry point sets the flag appropriately.

In `SharedPerDef` mode, `translateBinderType` caches the first
allocated universe name and reuses it.

### 3b. `SAWCoreLean.SAWModule.translateDataType` — set `PerBinder` mode

The existing code already calls `translateParams`, which threads
`translateBinder'` / `translateBinderType`. Under `PerBinder`,
each sort-0 param gets a fresh universe.

Also: `inductiveSort` computation (lines 176–179) is already
correct — `Lean.SortMax1Vars inductiveUniverses` emits `Sort (max
1 (max u1 u2 ...))`. Unchanged.

### 3c. `SAWCoreLean.SAWModule` / `translateDef` — set `SharedPerDef` mode

Ensure the def's body+type translation runs with a single shared
sort-0 universe. The `universeVars` state already collects all
allocated universe names; `mkDefinitionWith`'s `usedUniversesInDecl`
filter drops unused ones. For defs where `sort 0` never appears,
the shared universe is never allocated, so emits a pure-Type def
as today.

### 3d. Pretty-printer — unchanged

`Lean.SortVar u`, `Lean.SortMax1Vars us` already pretty-print
correctly. `SortMax1Vars` must include a `1` literal when the
max is over universes that could be `0` (i.e., all of them). Check:

```haskell
-- Language.Lean.Pretty — existing code for SortMax1Vars
-- Currently: max 1 (max u1 u2 ...)
```

Works whether `u_i = 0` or not.

## 4. Support-lib changes required

**None.** No new abbreviations, no new coercions, no new classes.
The proposed translator changes keep `SAWCorePreludeExtra.lean`
untouched.

Optional polish (not required for soundness):

- Audit `CryptolToLean.SAWCorePreludeExtra`'s `ite`, `iteDep`, etc.,
  to ensure they work for Prop motives. Probably already do since P4
  v2 universe-polymorphized them. Quick probe:

```lean
#check @CryptolToLean.SAWCorePreludeExtra.ite (True = True) Bool.true trivial trivial
```

## 5. Effort and risks

### Effort estimate

| Task | Estimate |
|---|---|
| Add `Sort0Mode` state flag + `translateBinderType` function | 30min |
| Wire `translateDataType` and `translateDef` entry points | 30min |
| Dedup-universe logic for SharedPerDef (cache first alloc) | 30min |
| Run generator, confirm `proveEqNat` and friends elaborate | 30min |
| Regression: re-check lines 1–2000 still elaborate | 30min |
| Edge-case probes (mixed sort-0 and sort-1 defs, isort) | 1h |

**Total: 3–4 hours.**

Much smaller than the preliminary PLift-insertion estimate (1 day)
because:
1. Uses existing P4 v2 infrastructure (`SortMax1Vars`).
2. No new support-lib code.
3. No need for per-app-site type comparisons in the translator.

### Risks

| # | Risk | Likelihood | Mitigation |
|---|---|---|---|
| 1 | `SharedPerDef` mode breaks a def where sort-0 binders really *should* be independent | low | None spotted in the SAWCore prelude; if found, case-by-case relax to `PerBinder` on that def (tag via SpecialTreatment) |
| 2 | Universe-polymorphic `Either` / `Maybe` breaks a handwritten use in scaffolding | low | Search scaffolding for direct references; none found |
| 3 | `Eq` between sort-0 binders in a def body forces shared universe; shared-universe rule holds | certain | Already probed |
| 4 | Subtle interaction with `isort` binders (Inhabited instance injection) | low | Probed C4 works |
| 5 | Sort-0 value-level `Sort 0` in `Eq (sort 0) a b` — translator emits `@Eq Type a b` today; what if value-level also polymorphic? | low-medium | Unchanged in this proposal. Value-level `Sort 0` stays as `Lean.Type`. `Eq` receives `Type` for its first arg. Works as today |

### Non-risks

- **Recursive concern (Q5)**: `natCompareLe` is a primitive (axiom).
  Nothing in the auto-translated Prelude pattern-matches on it. So
  no downstream unwrapping problem.
- **Dual concern (Q6)**: no Type-in-Prop-position errors in the
  current output; cumulativity is strictly one-way in practice.

## 6. Open questions

1. **SharedPerDef-mode implementation**: can we cache the allocated
   universe name in the `TermTranslationMonad` state, or do we need
   a Reader-layer override? The former is simpler; the latter is
   more hygienic (nested `withBinders` don't leak the shared-universe
   state to outer scopes).

2. **What about `isort 0`?** `isort 0` means "sort 0, with
   Inhabited-instance flag" — the binder gets an auto-injected
   `[Inh_a : Inhabited a]`. Under universe-poly mode, `Inhabited` must
   accept `Sort u`. The scaffolding's `Inhabited.{u}` already is, so
   this should just work. Worth a confirmation probe.

3. **Should we SpecialTreatment `Either` and `Maybe` to use a
   handwritten version instead (Approach D)?** Not necessary if
   Approach C lands, but simpler to ship as a workaround if C
   hits a snag during implementation.

4. **`Nat` vs `_root_.Nat` (Q1.1b) — fix in the same PR or separately?**
   Recommendation: separately. That's a scaffolding design question
   (binary-positive vs unary `Nat`), not a translator bug, and mixing
   it with this change muddies the review.

5. **`at` reserved keyword (Q1.1c) — fix in the same PR or separately?**
   Small and localized enough to bundle if convenient. Fix in
   `defaultIdentTarget` or similar: if the ident is in Lean's
   reserved-keyword set, quote with `«…»` or rename.

## 7. Confidence disclosure

- **Certain** (probed on concrete Lean): Approach C works for a
  verbatim copy of `proveEqNat`'s body with a universe-polymorphic
  `Maybe` and shared-universe `maybe`. No PLift needed.
- **Certain** (probed): Approach A (manual PLift) requires unwrapping
  at use sites, which the current translator doesn't do.
- **Certain** (probed): Approach B (CoeSort) fails when the
  translator emits explicit-universe-arg applications (`@foo (P :
  Prop) ...`), which the translator does emit.
- **Certain** (read from source): the P4 v2 translator already has
  `SortMax1Vars` and per-binder-fresh-universe machinery for sort-1;
  extending to sort-0 is additive.
- **Reasoned, not exhaustively probed**: the SharedPerDef rule
  preserves all currently-working sort-0 defs. I've probed it on
  `coerce__def`-style signatures and `proveEqNat`-style bodies; I
  have not enumerated every sort-0 def in the SAWCore prelude.
- **Unverified**: the translator change itself. The design doc is
  agreement-level, not implementation-level.

## 8. Probe file index

Saved in `/Users/miked/Projects/claude-lean-saw/deps/saw-script/.tmp/p6_probes/`
(sandbox blocks writes to `/tmp/`).

| File | Tests | Pass? |
|---|---|---|
| `A_manual_plift.lean` | Approach A signatures | yes |
| `A_soundness_check.lean` | A with pattern-match — needs `.down` | compiled |
| `B_coe_prop_type.lean` | Approach B basic CoeSort | yes |
| `B_coe_downstream.lean` | B with value construction | partial |
| `B2_coe_value.lean` | B + CoeHead to lift values | yes |
| `B3_coe_full.lean` | B full: CoeSort + CoeHead + Coe (PLift P) P | yes |
| `B_proveEqNat_full.lean` | B on verbatim `proveEqNat` | **FAIL** — @-forms |
| `B_debug_coe.lean`, `_coe2`, `_coe3`, `_coe4` | root-cause of B failure | confirms @-form issue |
| `C_universe_poly.lean` | Approach C polymorphic Either/Maybe | yes |
| `C2_universe_full.lean` | C + recursors + usage | yes |
| `C3_all_saw0_polymorphic.lean` | C with full sort-0 polymorphization on defs | yes (with test typos) |
| `C4_inhabited_interaction.lean` | C + Inhabited instance binders | yes |
| `C5_translator_sketch.lean` | what the translator would emit under C | yes |
| `C6_pairtype_poly.lean` | C on PairType | yes |
| `C7_eitherCong.lean` | Polymorphic eitherCong0 with u_x = u_y | yes |
| `C8_eq_unification.lean` | test: does Lean unify Eq args at different univs? | **NO** — forces shared |
| `C10b_full_poly_defs.lean` | confirms per-binder sort-0 breaks Eq | confirms |
| `C9_refined.lean` | Approach C*-asymmetric (inductives only) | partial fail |
| `C_star.lean` | C* with defs at `Type` — maybe fails | fails on `maybe` |
| `C_final.lean` | C with SharedPerDef mode | almost |
| `C_final2.lean` | cleaned C_final | **PASS** |
| `C_proveEqNat_full.lean` | C with full proveEqNat body | **PASS** |
| `C_soundness_check.lean` | C soundness audit | yes |
| `B_real_prelude_excerpt.lean` | B on literal prelude snippet | partial |
| `B_final_verify.lean`, `B_final_verify2.lean`, `B_verify3.lean` | B corner-case disambiguation (def-opacity matters for coercion firing) | mixed |
| `C_eitherCong_regression.lean` | Shared-universe regression check for eitherCong0 | yes |
| `C_isort_interaction.lean` | Q7 — isort+Inhabited+Sort u | yes |

## 9. Next steps

1. **Review this doc** — confirm Approach C is the right direction.
2. **Implement translator change 3a–3c** (3–4 hours).
3. **Regenerate Prelude** — verify all 17 Prop/Type errors resolve.
4. **Quality gate**: `lake env lean SAWCorePrelude.lean` reports only
   the 68 `_root_.Nat` and 13 `at`-keyword errors (separate follow-ups).
5. **Follow-up issue**: `_root_.Nat` scaffolding bug (Q1.1b).
6. **Follow-up issue**: `at` reserved-keyword escaping (Q1.1c).
