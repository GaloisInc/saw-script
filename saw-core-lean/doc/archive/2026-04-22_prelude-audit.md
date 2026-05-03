# Prelude-translation audit findings

*Draft — 2026-04-22 (audit agent report, lightly edited)*

This doc consolidates a structured audit of why the auto-translated
`SAWCorePrelude.lean` fails to elaborate, and what the correct —
sound — fixes are. It supersedes the earlier `2026-04-22_soundness.md`
conjecture that the problem is an unbridgeable `Eq`/`Prop` universe
gap (it isn't — that conjecture was wrong).

## Counts

Regenerating and running `lake env lean` on the output reports 70
errors (not 100 — we hit `maxErrors` before). Taxonomy:

- **41** `Type mismatch … has type Prop of sort Type but is expected
  to have type Type of sort Type 1` — cascading from group 1
- **28** `Application type mismatch` — split across groups 1, 2, 3
- **1** `Unknown constant Unit.rec` — group 4
- **~25** `Unknown constant Nat.NatPos`/`Nat.Zero` (behind the
  maxErrors cap) — group 3

## Group 1: universe polymorphism (~60 errors)

**The apparent `Eq`/`Prop` vs `Type 1` impedance was a red herring.**
Lean 4's `Eq.rec` is universe-polymorphic and happily accepts
`Prop`-returning motives.

The real issue: the translator's `translateSort` (in
`src/SAWCoreLean/Term.hs`) collapses every SAWCore sort (`sort 0`,
`sort 1`, `sort 2`, …) uniformly to Lean's bare keyword `Type` (=
`Type 0`). So our *emitted wrappers* like `Eq__rec`, `sym`, `trans`,
`eq_cong`, `uip`, `piCong0/1`, the `coerce__*` family, `fix`, `error`,
`unsafeAssert` are all **monomorphic at `Type 0`**. Their callers
then pass `t := Type` (Lean's `Type 0`, whose own type is `Type 1`),
and Lean rejects.

The proof this is a translator bug and not a semantic gap: a
similarly-shaped use of `@PairType.rec` (line 539 in the generated
output) works fine, because `PairType.rec` is a Lean-generated
recursor and is universe-polymorphic. Our wrappers fail only because
we wrote them monomorphically.

**Fix.** Extend the AST (done for the `Sort` type — see Phase-2C
commit `47eac7e`), then propagate the level through:

1. `src/SAWCoreLean/Term.hs:132-140`: `translateSort` passes through
   the level.
2. `src/Language/Lean/Pretty.hs`: `prettySort` emits `Type k`.
3. *Key extra step*: when a def's signature has a `sort k` for k ≥ 1,
   emit a universe-polymorphic version (e.g. `def Eq__rec.{u v}
   : …`). Requires opening fresh universe names in
   `SAWCoreLean.SAWModule` (or at the term-translation level) and
   carrying them through the emitted def.
4. For the motive in `Eq__rec` specifically — emit `Sort v` (not
   `Type v`) so it matches Lean core and accepts `Prop`-valued
   returns.

Fixes ~60 of the 70 errors. About a day of work.

## Group 2: `Bool.rec` constructor-order mismatch (~35 errors; also a **latent soundness bug**)

SAWCore declares `data Bool { True; False }` (True first).
Lean declares `data Bool | false | true` (false first).

Currently `SpecialTreatment.hs` maps `Prelude.Bool → Lean.Bool`,
`True → true`, `False → false`. Names line up, so use sites
*appear* correct. But when the SAWCore `Bool#rec1` reduction fires
on a translated `iteDep` or `ite`, the *case order* is swapped —
SAW's `iteDep p true fT fF = fT` becomes `Lean.Bool.rec fT fF true`,
which reduces to `fF` instead. **Silent runtime wrongness.**

Current demo.saw output may have this landmine sitting in the
generated Cryptol-primitive preludes where `bvAnd`/`bvOr`/`bvNot`/…
are defined via `Bool#rec1`.

**Fix.** Handwrite the permuting wrappers in a new
`CryptolToLean.SAWCorePreludeExtra.lean`:

```lean
namespace CryptolToLean.SAWCorePreludeExtra

/-- SAWCore's `iteDep` passes True-case first, False-case second
    — opposite of Lean's `Bool.rec`. -/
@[reducible] noncomputable def iteDep (p : Bool → Type) (b : Bool)
    (fT : p true) (fF : p false) : p b :=
  Bool.rec fF fT b

theorem iteDep_True (p : Bool → Type) (fT : p true) (fF : p false) :
    iteDep p true fT fF = fT := rfl
theorem iteDep_False (p : Bool → Type) (fT : p true) (fF : p false) :
    iteDep p false fT fF = fF := rfl

@[reducible] noncomputable def ite (a : Type) (b : Bool) (x y : a) : a :=
  Bool.rec y x b

theorem ite_eq_iteDep (a : Type) (b : Bool) (x y : a) :
    ite a b x y = iteDep (fun _ => a) b x y := rfl

end CryptolToLean.SAWCorePreludeExtra
```

Add SpecialTreatment `mapsTo` entries pointing `iteDep`, `iteDep_True`,
`iteDep_False`, `ite`, `ite_eq_iteDep` at these.

*Also* audit direct `Bool#rec`/`Bool#rec1` callers in the translator
output — any that don't go through `iteDep`/`ite` need similar
permuting wrappers or an error.

Half a day. Critical for soundness.

## Group 3: SAWCore `Nat` vs Lean `Nat` — **latent soundness bug**

`SpecialTreatment.hs:244` has `("Nat", mapsToCore "Nat")`. But:

- SAWCore: `data Nat { Zero; NatPos Pos; }` (binary-positive)
- Lean: `data Nat | zero | succ Nat` (unary)

These aren't structurally the same. Today the error surface is noisy
(~25 `Unknown constant Nat.NatPos`/`Nat.Zero` messages) because the
constructor names don't match. If someone "fixes" that naïvely by
renaming (`Zero → zero`, `NatPos → succ`), every `Nat#rec` in the
translated output starts quietly eliminating against Lean's unary
structure, producing wrong runtime behaviour.

**Fix.** Remove the `("Nat", mapsToCore "Nat")` entry. Let SAW's
`Nat` live as a native translated inductive at
`CryptolToLean.SAWCorePrelude.Nat`. If a consumer later needs a
bridge to Lean's `Nat`, add an explicit conversion in
`SAWCorePreludeExtra.lean`.

~1 hour. Soundness-critical — do immediately.

## Group 4: `UnitType__rec`

Lean's `Unit = abbrev PUnit.{1}` — no `Unit.rec`, only `PUnit.rec`.
The auto-translated `UnitType__rec` emits `@Unit.rec …`, which
Lean can't find.

**Fix** (recommended option): revert the `UnitType → Unit` and
`Unit → Unit.unit` mappings in `SpecialTreatment.hs`. Let SAW's
`UnitType` live as a native translated inductive. Rename its `Unit`
constructor to `TTUnit` (or similar) via `rename` to avoid the
collision with Lean's core `Unit`. The auto-generated
`UnitType.rec` then exists and everything works.

~1 hour.

## Subtly unsound currently-passing translations

Beyond groups 2 and 3 above, the audit flagged these:

1. **`unsafeAssert`**, **`coerce`**, **`fix`** are emitted as
   axioms. Sound in the sense that Lean is honest about them being
   unverified — but after group-1 fix they need to be universe-
   polymorphic axioms or they'll carry the same mismatch forward.

2. **`Prelude.Eq → Lean core Eq`** is actually fine. The earlier
   soundness doc's conjecture was wrong. `Eq.rec` being universe-
   polymorphic in Lean means it accepts `Prop` motives just like
   SAWCore does.

## Prioritized action list

| # | Work | Errors fixed | Soundness? | Effort |
|---|---|---|---|---|
| 1 | Group 3: remove `Nat → Nat` mapping | ~25 | **Critical**: eliminates a landmine | 1h |
| 2 | Group 2: Bool wrappers (iteDep, ite) | ~35 cascading | **Critical**: eliminates a silent runtime bug | 0.5d |
| 3 | Group 4: revert UnitType mapping | 2 | Cosmetic | 1h |
| 4 | Group 1: universe polymorphism | ~60 | Correctness (monomorphic wrappers are wrong) | ~1d |

Doing 1+2+3+4 should make the generated `SAWCorePrelude.lean`
elaborate cleanly. The `Rev.lean` demo output's 18
unknown-identifier errors go away once the preludes elaborate and
are checked into `saw-core-lean/lean/`.

## Correction to `2026-04-22_soundness.md`

The "Known approximations" section in that doc lists the
`Prelude.Eq` → Lean core `Eq` mapping under the heading "approximate
but let them fail." That characterization is **wrong**: the mapping
is in fact semantically exact. The observed failures come from our
own monomorphic wrapper emission (group 1 here), not from a
fundamental impedance. Fixing group 1 makes those defs elaborate;
no approximation is involved.

Update that doc when group 1 lands.
