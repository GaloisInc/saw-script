# Audit: handwritten SAWCorePrimitives fidelity vs. SAWCore source

*2026-04-24*

Scope: for every declaration in `saw-core-lean/lean/CryptolToLean/`
(primary: `SAWCorePrimitives.lean`; supporting: `SAWCoreScaffolding`,
`SAWCoreVectors`, `SAWCoreBitvectors`, `SAWCorePreludeExtra`) check
against the SAW source at `saw-core/prelude/Prelude.sawcore` and
`cryptol-saw-core/saw/Cryptol.sawcore` that the Lean realisation
denotes the same thing.

Verdict up front: **no hard soundness bugs were found.** Every
inductive matches SAW's data-decl (constructor count, order, and
argument types). Every axiom matches SAW's primitive/axiom
signature after accounting for the translator's sort-collapse
(sort/isort k -> Type). Three ⚠ caveats are noted below. One dead
`mapsTo` entry (`bitvector`) is noted; it is inert, not unsound.

Layout:

- Fidelity table — one row per declaration.
- Caveats — explanatory notes for every ⚠.
- Bugs — (empty) would hold ✗ entries.
- Unchecked corners — the known residual risk.

## Fidelity table

| Declaration | SAW source (file:line) | Lean realisation (file:line) | Verdict | Notes |
|---|---|---|---|---|
| `Either s t : sort 0`, ctors `Left, Right` | `Prelude.sawcore:905` | `SAWCorePrimitives.lean:36` | ✓ | Param count 2, order `s, t`. Ctor order Left-then-Right matches; auto-gen `Either.rec` has case order `Left, Right` matching SAW's `Either__rec`. |
| `Num : sort 0`, ctors `TCNum : Nat -> Num, TCInf : Num` | `Cryptol.sawcore:43` | `SAWCorePrimitives.lean:51` | ✓ | Ctor order `TCNum, TCInf` matches. |
| `Stream a : sort 0`, ctor `MkStream : (Nat -> a) -> Stream a` | `Prelude.sawcore:1997` | `SAWCorePrimitives.lean:70` | ✓ | Single ctor, signature matches. |
| `EmptyType : sort 0`, ctor `Empty` | `Prelude.sawcore:366` | `SAWCorePrimitives.lean:77` | ✓ | Single-ctor, no args. |
| `RecordType (s:String)(a b :sort 0) : sort 0`, ctor `RecordValue : a -> b -> RecordType s a b` | `Prelude.sawcore:376` | `SAWCorePrimitives.lean:83` | ✓ | Params `s, a, b`, ctor takes `a, b` in that order. |
| `Integer : sort 0` (primitive) | `Prelude.sawcore:2090` | `SAWCorePrimitives.lean:91` + `SpecialTreatment.hs:261` remaps `Integer -> Int` at use sites | ✓ | The `axiom Integer : Type` in primitives is a placeholder; all use sites go through `mapsToCore "Int"`. |
| `bit0_macro n := 2 * n` | `Prelude.sawcore:963-967` (`Bit0 : Pos -> Pos`, `Bit0 p = 2*p`) | `SAWCorePrimitives.lean:64` | ✓ | Value-level match. See `2026-04-24_audit-nat-mapping.md` for the elimination-level caveat that this predates. |
| `bit1_macro n := 2 * n + 1` | `Prelude.sawcore:963-967` (`Bit1 p = 2*p+1`) | `SAWCorePrimitives.lean:65` | ✓ | Same caveat as `Bit0`. |
| `addNat : Nat -> Nat -> Nat := Nat.add` | `Prelude.sawcore:1097` | `SAWCorePrimitives.lean:104` | ✓ | Defined via `Nat#rec` in SAW to exactly `+` on N. Lean's `Nat.add` agrees. |
| `subNat : Nat -> Nat -> Nat := Nat.sub` | `Prelude.sawcore:1252` (`subNat x y = ZtoNat (subNZ x y)`) | `SAWCorePrimitives.lean:105` | ✓ | Both saturate at 0. |
| `intAdd : Int -> Int -> Int` | `Prelude.sawcore:2092` | `SAWCorePrimitives.lean:107` | ✓ (axiom) | Declared as opaque; signature matches. Not evaluable. |
| `intSub, intMul, intDiv, intMod, intNeg` | `Prelude.sawcore:2093-2099` | `SAWCorePrimitives.lean:108-112` | ✓ (axiom) | Signatures match. |
| `intEq : Int -> Int -> Bool` | `Prelude.sawcore:2101` | `SAWCorePrimitives.lean:113` | ✓ (axiom) | Boolean equality on integers — matches SAW. |
| `intLe : Int -> Int -> Bool` | `Prelude.sawcore:2102` | `SAWCorePrimitives.lean:114` | ✓ (axiom) | Boolean ≤ (not <). SAW name is `intLe`, matches. (SAW also has `intLt` at line 2103 — not yet mapped; see §Unchecked corners.) |
| `natToInt : Nat -> Int`, `intToNat : Int -> Nat` | `Prelude.sawcore:2106-2107` | `SAWCorePrimitives.lean:115-116` | ✓ (axiom) | SAW's `intToNat x = max 0 x`; not enforced on Lean side (axiom-only), fine. |
| `gen : (n : Nat) -> (a : Type) -> (Nat -> a) -> Vec n a` | `Prelude.sawcore:1533` | `SAWCorePrimitives.lean:121` | ✓ (axiom) | Param order `n, a, f` matches SAW's `n, a, f`. |
| `atWithDefault : (n:Nat) -> (a:Type) -> a -> Vec n a -> Nat -> a` | `Prelude.sawcore:1561` | `SAWCorePrimitives.lean:124` | ✓ (axiom) | Arg order `n, a, d, v, i` matches. |
| `foldr : (a b:Type) -> (n:Nat) -> (a -> b -> b) -> b -> Vec n a -> b` | `Prelude.sawcore:1600` | `SAWCorePrimitives.lean:127` | ✓ (axiom) | Arg order and f's `a -> b -> b` match. |
| `foldl : (a b:Type) -> (n:Nat) -> (b -> a -> b) -> b -> Vec n a -> b` | `Prelude.sawcore:1601` | `SAWCorePrimitives.lean:130` | ✓ (axiom) | Arg order and f's `b -> a -> b` (swapped vs. foldr) match. |
| `coerce : (a b : Type) -> @Eq Type a b -> a -> b` | `Prelude.sawcore:217` (`primitive coerce : (a b : sort 0) -> Eq (sort 0) a b -> a -> b`) | `SAWCorePrimitives.lean:135` | ✓ | SAW's `Eq (sort 0) a b` maps to Lean's `@Eq Type a b`; the `mapsToCoreExpl "Eq"` entry (SpecialTreatment.hs:265) ensures explicit-type applications line up. |
| `unsafeAssert.{u} : (α : Sort u) -> (x y : α) -> @Eq α x y` | `Prelude.sawcore:212` (`axiom unsafeAssert : (a : sort 1) -> (x y : a) -> Eq a x y`) | `SAWCorePrimitives.lean:140` | ⚠ | See caveat 1. |
| `error.{u} : (α : Sort u) -> String -> α` | `Prelude.sawcore:121` (`primitive error : (a : isort 1) -> String -> a`) | `SAWCorePrimitives.lean:144` | ⚠ | See caveat 2 (the more concerning of the three). |
| `iteDep.{u} (p : Bool → Sort u) (b : Bool) (fT : p true) (fF : p false) : p b` | `Prelude.sawcore:464` | `SAWCorePreludeExtra.lean:40` | ✓ | Arg order matches SAW (True-case before False-case); body `Bool.rec fF fT b` correctly permutes to Lean's false-before-true order. `rfl` lemmas verify the reduction rules. |
| `iteDep_True`, `iteDep_False` | `Prelude.sawcore:468-476` | `SAWCorePreludeExtra.lean:45, 49` | ✓ | Both `rfl`-proven; match SAW's `Refl`-based equalities. |
| `ite.{u} (a : Sort u) (b : Bool) (x y : a) : a` | `Prelude.sawcore:479` (`ite : (a : sort 1) -> Bool -> a -> a -> a`) | `SAWCorePreludeExtra.lean:54` | ✓ | True-case before False-case preserved by `Bool.rec y x b`. |
| `ite_eq_iteDep` | `Prelude.sawcore:483` | `SAWCorePreludeExtra.lean:58` | ✓ | `rfl`-proven. |
| `Vec n α := Vector α n` | `Prelude.sawcore:1530` (`primitive Vec : Nat -> sort 0 -> sort 0`) | `SAWCoreVectors.lean:14` | ⚠ | See caveat 3. |
| `bitvector n := Vec n Bool` | *not present as a SAW ident* (see Unchecked corners §1) | `SAWCoreBitvectors.lean:26` | ✓ (definition) / dead `mapsTo` | The Lean abbrev matches the customary definition used in SAW tooling (`bitvectorType` at `OpenTerm.hs:338` also expands as `Vec n Bool`). The SpecialTreatment entry `("bitvector", mapsTo …)` (SpecialTreatment.hs:299) routes a name SAW never emits — inert. |
| `Bit := Bool` | (SAW has no `Bit` ident in Prelude.sawcore; `Bit` shows up as an emitted alias in cryptol-saw-core at the Haskell level) | `SAWCoreScaffolding.lean:13` | ✓ | SAW's `Bool` (True/False) maps to Lean's `Bool` (false/true); the `iteDep/ite` wrappers handle elimination order, so aliasing `Bit := Bool` is consistent. No elimination happens through `Bit` directly. |
| `Inhabited.{u}` class | n/a (no SAW counterpart — this is a scaffolding class) | `SAWCoreScaffolding.lean:26` | ⚠ (stale) | See caveat 4. |

## Caveats

### 1. `unsafeAssert` is universe-polymorphic; SAW's is `sort 1`-only

SAW: `axiom unsafeAssert : (a : sort 1) -> (x y : a) -> Eq a x y`.
Lean: `axiom unsafeAssert.{u} : (α : Sort u) → (x y : α) → @Eq α x y`.

Discrepancy: Lean's `u` is unconstrained, so `α : Prop` and
`α : Type u` for arbitrary `u` are both permitted. SAW forbids
both (sort 1 is specifically Type-at-level-0 in SAW's hierarchy,
which this translator collapses to Lean's `Type`).

Does it matter? The translator collapses every SAW `sort k` to
Lean's `Type` (see `translateSort` in `SAWCoreLean/Term.hs:148`), so
every SAW-emitted use site has `α : Type` and Lean infers `u = 1`.
At `u = 0` (α : Prop) the axiom is *vacuous* in Lean — `@Eq α x y`
for two proofs of a proposition is already provable by proof
irrelevance, so no new unsoundness is created. At `u > 1` the
axiom is strictly stronger than SAW's but no SAW-produced term can
instantiate Lean's `u > 1` (sorts have been collapsed). **No
translator-reachable hole.**

If a downstream Lean user manually invokes `unsafeAssert` outside
translated code, the axiom lets them assert equalities SAW also
lets them assert (SAW's `unsafeAssert` is already globally
available to translated theorems). So this is not a regression.

### 2. `error` is universe-polymorphic; SAW's is `isort 1`-only

SAW: `primitive error : (a : isort 1) -> String -> a`.
Lean: `axiom error.{u} : (α : Sort u) → String → α`.

This is the **only** primitive where the universe-polymorphic Lean
form is genuinely more permissive in a way that could produce a
proof of False:

- At `u = 0`, `α : Prop`, and `error False ""` inhabits `False`.
- SAW's `isort 1` is the *inhabited* sort-1 types, which exclude
  uninhabited propositions like `False`. SAW's `error` would not
  type-check on `False`.

Does it matter today? The translator's sort-collapse means
SAW-produced use sites have `α : Type`, instantiating Lean's
`u = 1`. The translator never emits `error P ""` with `P : Prop`
because SAW terms never have that shape post-specialization. So
no SAW → Lean translation can exploit this.

The hole exists for *hand-written Lean proofs* that invoke
`CryptolToLean.SAWCorePrimitives.error` directly. A user-authored
theorem could prove False by `exact error False ""`.

**Proposed fix.** Tighten the Lean axiom's signature to match
SAW's sort-1-and-inhabited intent:

```lean
axiom error : (α : Type) → String → α
```

(Monomorphic at Lean's `Type`, matching the translator's sort
collapse.) If future demand needs `Prop`-valued `error`, we can
add a separate `errorProp : (p : Prop) → [Nonempty p] → String → p`
that at least requires evidence of inhabitance.

Alternatively, gate the universe:

```lean
axiom error.{u} : (α : Sort (u+1)) → String → α
```

which excludes `u = 0` (α : Prop). This keeps polymorphism across
`Type`, `Type 1`, … but not Prop.

This isn't a *translator-reachable* soundness bug, but the
handwritten library is the attack surface for any Lean user
importing the module, and "the translator would never emit that"
is a weaker guarantee than the axiom's shape itself implies.
Worth tightening.

### 3. `Vec n α := Vector α n` exposes Lean's `Vector.mk` / `Vector.rec` beyond SAW's surface

SAW: `primitive Vec : Nat -> sort 0 -> sort 0;` (opaque; only the
eliminators `gen, head, tail, atWithDefault, foldr, foldl, zip,
scanl, EmptyVec, ConsVec` and various axioms about them have
content).

Lean: `abbrev Vec n α := Vector α n`, where `Vector α n` is a
single-constructor `structure` with fields `toArray : Array α` and
`size_toArray : toArray.size = n`. That gives us `Vector.mk`,
`Vector.rec`, and direct equality on `Array α`.

Discrepancy: the Lean type has *more structure* than SAW
guarantees. In particular:

- `Vector.mk #[1,2,3] rfl = Vector.mk #[1,2,3] rfl` holds by `rfl`
  in Lean (after the proof-irrelevance pass over `size_toArray`).
  This is stronger than anything SAW's axiomatic presentation
  gives.
- `Vector.rec` lets a Lean user pattern-match directly on the
  underlying `Array`, reaching inside the abstraction SAW
  maintains.

Does it matter? Under the specialization architecture the
translator emits `Vec`-valued terms only via `gen`,
`atWithDefault`, `foldr`, `foldl`, and ctor/recursor routes through
`SAWCorePrimitives.Either.rec` etc. — never `Vector.mk` or
`Vector.rec`. A downstream Lean proof about a translated theorem
*could* reason via `Vector.mk`/`Vector.rec`, and any equality
lemmas they prove that way are Lean-valid but not guaranteed to
correspond to a SAW-derivable fact.

In practice this is fine because:

1. The eliminators are axioms with no reduction rules, so Lean
   can't *compute* `gen 3 Bool f` into a `Vector.mk` form. The
   Lean user's "extra" theorems about `Vector.mk` are about values
   they construct themselves, not about values produced by
   translation.
2. The Rocq backend takes the same approach (maps `Vec` to Rocq's
   `Vector`), so this is a known and accepted abstraction leak.

**Not a bug, but a structural caveat** worth noting. A tighter
alternative would be to define `Vec n α` as an opaque `axiom Vec :
Nat -> Type -> Type` with corresponding axioms for each
eliminator, mirroring SAW more literally. The current abbrev-based
shape is chosen for ergonomics (users get Lean's library of
`Vector` lemmas), at the cost of this leak.

### 4. `SAWCoreScaffolding.Inhabited` is stale

The auto-injection of `[Inh_a : Inhabited a]` instance binders on
`isort` parameters was removed (see `Term.hs:196-209` comment).
The `class Inhabited.{u} (α : Sort u)` + core-Inhabited-bridge
instance in `SAWCoreScaffolding.lean:26-33` is no longer
referenced by the translator.

Does it matter? It's dead code. Keeping it doesn't hurt
soundness. A future translator that re-introduces the auto
injection would want it back, so there's a small argument for
leaving it. But in its current unreferenced state it's noise
and could mislead an auditor reading `SAWCoreScaffolding.lean`
and assuming the class is live.

**Proposed action.** Either delete the `Inhabited` class from
scaffolding (preferred, per the "don't keep stale scaffolding"
principle) and rely on Lean core's `_root_.Inhabited` if/when the
translator needs it, or leave an explicit comment flagging the
class as dormant with a reference to the `Term.hs:196` explanation.

## Bugs (✗)

*None found.*

## Unchecked corners

1. **`bitvector` as a SAW identifier.** The `mapsTo` entry
   `("bitvector", …)` at `SpecialTreatment.hs:299` routes a name I
   could not find as a top-level ident in either `Prelude.sawcore`
   or `Cryptol.sawcore`. The translator's `OpenTerm.hs:338`
   builds bitvector types at the Haskell level as `Vec n Bool`
   without naming them. So this entry appears inert — a reference
   to a nonexistent SAW ident. **Not a bug (dead route), but
   should either be removed from `SpecialTreatment.hs` or a
   comment added explaining why it's kept.** The Lean-side
   abbrev is still useful for handwritten proofs and other
   tooling, so `SAWCoreBitvectors.lean` itself is fine to keep.

2. **`List`, `Cons`, `Nil`.** Not currently in SpecialTreatment.
   If/when a demo exercises them, we will need Lean-side
   realisations and a special-treatment entry. The Prelude
   defines them at line 2171; ctor order is `Nil, Cons`.

3. **`intLt`, `intMin`, `intMax`, `intAbs`.** Present in
   `Prelude.sawcore:2097-2103` but not mapped. Not yet needed;
   add when demos surface them.

4. **SAW's `Eq` lives in `Prop` but with `t : sort 1`.**
   The SAW source says `data Eq (t : sort 1) (x : t) : t -> Prop
   where Refl : Eq t x x` (line 137). Mapping to Lean's
   `@Eq Type α β` = `α = β` is correct *at the level SAW uses
   it* (equality of types-in-Type, equality of terms-in-Type).
   But SAW's `Eq a x y` with `a : Prop` would be `Eq Prop p q`
   — equality of two propositions. Our mapping routes SAW's
   `Eq` to Lean's `Eq` with type made explicit; Lean's `Eq` is
   universe-polymorphic and handles both. Nothing to fix here
   — the universe polymorphism in Lean's `Eq` happens to line
   up. Flagged because a reviewer should confirm with me that
   "SAW emits `Eq (sort 0) …` only" after specialization.

5. **Number-kind arithmetic.** The `Num` inductive is declared,
   but the Cryptol numeric-kind operations (`tcAdd`, `tcMul`,
   `tcMin`, etc. from `Cryptol.sawcore:55-250`ish) are not in
   SpecialTreatment. Presumably they're reduced away by
   specialization for the current demos; a future demo that
   retains symbolic `Num`-arithmetic would need them.

6. **Vector `Vector.mk` leakage.** Per caveat 3 — not a bug, but a
   human should sign off that the ergonomic trade-off is worth
   it.

## Summary

- 5 inductives: all ✓ (constructor order, count, signatures match
  SAW).
- 11 opaque type/arithmetic axioms: all ✓ signature-wise.
- 6 vector/transport axioms (`gen`, `atWithDefault`, `foldr`,
  `foldl`, `coerce`, `unsafeAssert`, `error`): 4 ✓, 2 ⚠
  (`unsafeAssert`, `error` — universe polymorphism beyond SAW's
  `sort 1` / `isort 1`, concrete concern only for `error` at Prop).
- 4 `SAWCorePreludeExtra` `ite`/`iteDep` wrappers: all ✓; the
  `Bool.rec` permutation is correct; `rfl` reductions go through.
- Type aliases (`Vec`, `bitvector`, `Bit`): all ✓ at the type
  level; `Vec`'s structural leakage flagged as ⚠.
- Scaffolding `Inhabited` class: ⚠ stale.

Action items in priority order:

1. **Tighten `error`'s Lean signature** to close the
   `error False ""` hole (Caveat 2). Suggested forms in that
   section.
2. Remove or document the dead `bitvector` SpecialTreatment entry
   (Unchecked corner 1).
3. Remove stale `Inhabited` class from `SAWCoreScaffolding.lean`
   (Caveat 4) — or mark it dormant.
4. Decide on the `Vec` vs `Vector` abstraction leak (Caveat 3):
   accept it (document), or re-axiomatise `Vec` opaquely.
