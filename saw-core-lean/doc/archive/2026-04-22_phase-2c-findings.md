# Phase 2C findings: first-pass generated prelude output

*Draft — 2026-04-22*

After landing Phase 2A (SAWModule walker) and Phase 2B (prelude
generator commands), a first run of `write_lean_sawcore_prelude` and
`write_lean_cryptol_primitives_for_sawcore` against the real SAWCore
sources completes without crashing. The output is sizable:

- `SAWCorePrelude.lean`: 4 785 lines (from 2 628 lines of
  `Prelude.sawcore`)
- `CryptolPrimitivesForSAWCore.lean`: 16 643 lines (from 2 180 lines
  of `Cryptol.sawcore`)

Neither file currently elaborates under Lean. This document catalogs
the concrete issues surfaced by `lake env lean` on the generated
preludes, with proposed resolutions. Each is a Phase-2C work item.

## 1. Recursor / `noncomputable` machinery

**Symptom.** Lean reports
`code generator does not support recursor Foo.rec`
on every def whose body invokes `.rec`. Cascading, every downstream
def fails with `failed to compile definition … marked noncomputable`.

**Root cause.** Lean 4 permits `.rec` only inside `noncomputable def`s
(or in proofs). SAWCore's eliminators are used freely in ordinary
definitions.

**Fix.** Emit `noncomputable def` for any def whose body contains a
reference to a `.rec` eliminator. Two sub-options:

- **Conservative:** always emit `noncomputable def` for definitions
  translated by the SAWModule walker. Correct, trades compilability
  for run-time performance — generated-prelude output isn't meant to
  be run.
- **Smart:** static-walk the translated body looking for `.rec`
  references. More work, tighter output.

Recommendation: go conservative. Run-time performance of the
*generated prelude* is irrelevant; the translator isn't a compiler.

AST change: add a `noncomputable` flag to `Lean.Definition`, or
introduce a new `NoncomputableDefinition` variant. The flag is
cleaner.

## 2. Recursor naming convention

**Symptom.** Lean rejects `Eq.Refl`, `Eq.Sym` etc. (title-cased
constructor references) because Lean uses lowercase `Eq.refl`,
`Eq.symm`.

**Root cause.** Two different issues intertwined:

- Lean's *built-in* `Eq` uses `Eq.refl` / `Eq.symm`. Those names
  differ from the SAWCore-prelude-named constructors `Eq.Refl` /
  `Eq.Sym`. Because we map SAWCore `Prelude.Eq` → Lean core `Eq`, the
  constructors need to map too.
- For SAWCore-native datatypes we keep, Lean will auto-generate
  constructors under whatever casing we emit. Mixed case is
  consistent with SAWCore's own convention and works for those.

**Fix.** Add SpecialTreatment entries for Lean-core constructors:

```haskell
, ("Refl", mapsToCoreExpl "Eq.refl")
-- (Sym has no direct Lean analog; generate from Prelude.sawcore)
```

Catalogue the full list by elaborating the generated prelude and
collecting each `Unknown constant` error that points at a Lean-core
mismatch.

## 3. Anonymous-binder name collisions

**Symptom.** Uncommon-looking identifiers like `_'`, `_''`, `_'''`
in generated output. Valid Lean, but ugly, and can potentially
collide if a user happens to name something `_'`.

**Root cause.** SAWCore's convention is `_` for anonymous binders,
but our `reservedIdents` includes `_`, so `freshVariant` appends
`'`s until it's not in use.

**Fix.** When a binder's SAWCore name is `_` and the body doesn't
reference it, emit a truly anonymous `PiBinder Explicit Nothing`
instead of a named `_'`. For lambdas (which always need a name),
either use a single fresh name like `unused` or collapse
consecutive `_` binders via Lean's `(_ : A) (_ : B)` syntax (Lean
accepts `_` as an unnamed lambda binder).

Reference Rocq behaviour: it emits `_` for anonymous binders in Pi
position; for lambda, Rocq's `translateBinder` generates fresh names
unconditionally (hence similar ugliness in Rocq output, which works
because Coq doesn't reserve `_`).

## 4. SAWCore's `UnitType` vs. Lean's `Unit`

**Symptom.** `Application type mismatch: The argument Unit has type
Type of sort Type 1 but is expected to have type UnitType of sort
Type`.

**Root cause.** Lean has `Unit : Type` and `Unit.unit : Unit` in
core. SAWCore's prelude defines `UnitType : sort 0` with constructor
`Unit : UnitType`. Since the inductive lives in our namespace
(`CryptolToLean.SAWCorePrelude.UnitType`), the constructor should be
`UnitType.Unit` — but Lean's name resolution finds its own `Unit`
first.

**Fix.** Two options:

- Rename SAWCore's `Unit` constructor to something non-colliding in
  the generated output (`TTUnit`, or `UnitType.unit` lowercased).
- Skip SAWCore's `UnitType` entirely via `DefSkip` and map it to
  Lean's core `Unit` via SpecialTreatment.

Recommendation: the second. Native Lean `Unit` is a drop-in
replacement.

```haskell
, ("UnitType", mapsToCore "Unit")
, ("Unit",     mapsToCore "Unit.unit")
```

## 5. Constructor-parameter-handling redux

**Symptom.** After the Phase-2B fix (emit `@` for constructors),
most constructor applications elaborate. But some still fail:
`PairType.PairValue ?m.3 ?m.4 … is being applied to the argument x`.

**Root cause.** Pending inspection. Plausible that Lean still infers
the datatype parameters implicitly even under `@`, or that the
argument ordering in SAWCore's constructor type differs from Lean's
generated one.

**Fix.** Pending investigation once the recursor / noncomputable
issues are cleared — they were fouling the earlier elaboration path.

## 6. Universe polymorphism

**Symptom.** Some defs fail with `Type of sort Type 1`.

**Root cause.** Our AST's `Sort` only has `Prop | Type` — no universe
level. All SAWCore sorts collapse to `Type`. When the SAWCore source
genuinely mixes sorts (e.g., `Prelude.sawcore` distinguishes `sort 0`
from `sort 1`), the translator conflates them.

**Fix.** Extend `Language.Lean.AST.Sort` to `Sort (Maybe Nat)`, where
`Nothing` means "defer to Lean's inference." Pretty-printer emits
`Type`, `Type 0`, `Type 1` accordingly. Translator side: extend
`translateSort` to pass through the SAWCore sort index.

## 7. Prelude's `fix` axiom

**Symptom.** None currently; emitted cleanly as `axiom fix`.

**Status.** Working as designed per the Phase-1 decision ("primitives
become axioms"). A Phase-4 `termination_by` rewrite might replace
this with a real recursion, but not needed for closing Phase 2.

## 8. What's working cleanly

- Non-recursive def translation: `id`, `sawLet`, `PairType_def`, most
  constant wrappers.
- Inductive declarations: `UnitType`, `PairType`, `Nat`, `List`, …
  are all emitted structurally correctly; it's their *uses* that
  break due to issue #1.
- Namespace wrapping: `namespace CryptolToLean.SAWCorePrelude … end`
  parses.
- Inhabited-instance injection (Phase-1 audit response) interacts
  correctly — emitted `[Inh_a : Inhabited a]` binders don't cause any
  new failures.
- Preamble imports: `import CryptolToLean` resolves, pulling in the
  three handwritten stubs.

## 9. Phase 2C sub-tasks

In priority order, each a likely separate commit:

1. Add a `noncomputable` flag to `Lean.Definition` and set it when
   emitting prelude defs. Fixes issue #1 and its transitive effects.
2. SpecialTreatment entries for Lean-core primitives in the prelude:
   `UnitType`/`Unit` (#4), `Eq.refl`/`Eq.symm` (#2), likely more.
3. Re-run generators and catalog remaining errors.
4. Anonymous-binder cleanup (#3) — quality, not correctness.
5. Universe-polymorphism support (#6).
6. Revisit constructor application parameter handling (#5) once the
   rest is cleared.

Rough estimate to close these: 1-2 days. After which the generated
preludes should `lake build` end-to-end, and Phase 2D
(`write_lean_cryptol_module` + the full saw-lean-example run) is
unblocked.
