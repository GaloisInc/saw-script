/-
# Phase 2.6 universe stress probe

Hand-written Lean targets for the SAWCore-Prelude shapes the
auto-emit machinery (Phase 3) must reproduce. Each section pins one
representative shape, with the SAWCore source comment alongside the
Lean translation it expects.

If a probe fails to elaborate, the corresponding target shape needs
revision BEFORE Phase 3 wires the auto-emitter to it.

Universe-rule recap (per Phase 0 + Phase 2.2):
* SAW `(t : sort 1)` at binder position → Lean `(t : Sort u_n)`,
  with `u_n` fresh per occurrence — never shared across binders.
* SAW `sort 0` as a value (e.g. `Eq (sort 0) a b`) → Lean `Type`,
  a value of type `Type 1 = Sort 2`.
* Polymorphic-target call sites use the mathport pattern
  `@Foo.{u_args, …}` for every level the callee declares,
  bypassing Lean's universe unifier.

The auto-emitted prelude uses `Eq__rec`, `eq_cong`, `coerce__def`,
etc. as wrappers around Lean built-ins (cf. universe_probe.lean for
those three). This file extends coverage to the rest.
-/

namespace UniverseStress

/-! ## 1. `sawLet` — two-binder polymorphism on independent universes

SAW: `sawLet : (a b : sort 1) -> a -> (a -> b) -> b`

Two independent `sort 1` binders → two fresh universes. -/
noncomputable def sawLet.{u₁, u₂}
    (a : Sort u₁) (b : Sort u₂)
    (x : a) (f : a → b) : b :=
  f x

/-! ## 2. `id` (sort-0 binder) — degenerate case, no universe

SAW: `id : (a : sort 0) -> a -> a`. Sort 0 at binder position
emits `Type` directly (the Phase 0 rule), no universe variable. -/
def id_sort0 (a : Type) (x : a) : a := x

/-! ## 3. `error` — single universe, axiom

SAW: `primitive error : (a : isort 1) -> String -> a`.
`isort 1` is the inhabited variant of `sort 1`; same universe
shape, additional advisory flag we drop on translation. -/
axiom error_poly.{u} : (a : Sort u) → String → a

/-! ## 4. `elimVoid` — universe of return type

SAW: `elimVoid : (a : sort 1) -> Void -> a`. Lean has its own
`Empty.elim` but we mirror the SAW shape exactly. -/
noncomputable def elimVoid.{u} (a : Sort u) : Empty → a :=
  fun e => e.elim

/-! ## 5. `sym` / `trans` — single carrier universe, Prop motive

SAW: `sym : (a : sort 1) -> (x y : a) -> Eq a x y -> Eq a y x`.
The `Eq` motive lands in Prop (universe 0). -/
noncomputable def sym.{u}
    (a : Sort u) (x y : a) (h : @Eq.{u} a x y) : @Eq.{u} a y x :=
  @Eq.symm.{u} a x y h

noncomputable def trans.{u}
    (a : Sort u) (x y z : a)
    (h1 : @Eq.{u} a x y) (h2 : @Eq.{u} a y z) : @Eq.{u} a x z :=
  @Eq.trans.{u} a x y z h1 h2

/-! ## 6. `eq_inv_map` — two-universe with cross-universe Eq

SAW: `eq_inv_map : (a b : sort 1) -> (a1 a2 : a) -> Eq a a1 a2 ->
                    (f1 f2 : a -> b) -> Eq b (f1 a2) (f2 a2) ->
                    Eq b (f1 a1) (f2 a1)`.

Two independent universes; the second `Eq` lives at universe of
`b`. -/
noncomputable def eq_inv_map.{u₁, u₂}
    (a : Sort u₁) (b : Sort u₂)
    (a1 a2 : a) (h_a : @Eq.{u₁} a a1 a2)
    (f1 f2 : a → b) (h_b : @Eq.{u₂} b (f1 a2) (f2 a2))
    : @Eq.{u₂} b (f1 a1) (f2 a1) :=
  @Eq.rec.{0, u₁} a a2
    (fun y _ => @Eq.{u₂} b (f1 y) (f2 y))
    h_b
    a1 (@Eq.symm.{u₁} a a1 a2 h_a)

/-! ## 7. `PairType1` — data type with sort-1 fields

SAW: `data PairType1 (a b : sort 1) : sort 1 where {
        PairValue1 : a -> b -> PairType1 a b; }`.

Lean's inductive equivalent. The `max` rule: return sort is
`Sort (max u₁ u₂ 1)` (Lean inductives can't return Prop unless
they're explicitly Prop). The auto-emit machinery emits
`Sort (max u_a u_b 1)` for non-Prop inductives. -/
inductive PairType1.{u₁, u₂} (a : Sort u₁) (b : Sort u₂)
    : Sort (max u₁ u₂ 1)
  | PairValue1 : a → b → PairType1 a b

noncomputable def fstPairType1.{u₁, u₂}
    (a : Sort u₁) (b : Sort u₂)
    (p : @PairType1.{u₁, u₂} a b) : a :=
  match p with
  | PairType1.PairValue1 x _ => x

noncomputable def sndPairType1.{u₁, u₂}
    (a : Sort u₁) (b : Sort u₂)
    (p : @PairType1.{u₁, u₂} a b) : b :=
  match p with
  | PairType1.PairValue1 _ y => y

/-! ## 8. `uncurry1` — three-universe def

SAW: `uncurry1 (a b c : sort 1) (f : a -> b -> c)
                (x : PairType1 a b) : c`. -/
noncomputable def uncurry1.{u₁, u₂, u₃}
    (a : Sort u₁) (b : Sort u₂) (c : Sort u₃)
    (f : a → b → c) (x : @PairType1.{u₁, u₂} a b) : c :=
  match x with
  | PairType1.PairValue1 p q => f p q

/-! ## 9. Nested polymorphism — function-typed binders

SAW pattern: `(f : (a : sort 1) → a → a) → …`. A binder whose type
is a Pi over a sort-1 binder. Auto-emit needs to recurse into the
Pi body when allocating universes.

NOTE: `Bool : Type` has type `Sort 1`. Calling `f` (which expects
`Sort u` for an outer-bound `u`) on `Bool` forces `u := 1`. We
take the polymorphic-input function and only call it at universe
1, so the function-type-binder gets `u₀ := 1` at that callsite. -/
noncomputable def applyToBool (f : (a : Type) → a → a) : Bool :=
  f Bool false

/-! ## 10. `unsafeAssert` — axiom, single universe

SAW: `axiom unsafeAssert : (a : sort 1) -> (x : a) -> (y : a) ->
                            Eq a x y`. Universe-polymorphic axiom
that the auto-emit machinery surfaces as a Lean `axiom` decl. -/
axiom unsafeAssert_poly.{u} :
  (a : Sort u) → (x y : a) → @Eq.{u} a x y

/-! ## 11. `EqDep` — dependent equality data type

SAW: `data EqDep (t : sort 1) (P : t -> sort 0) (x : t) (p : P x)
                : (y : t) -> P y -> Prop where {
        ReflDep : EqDep t P x p x p; }`.

`(t : sort 1)` → `u₁`; `(P : t -> sort 0)` is a value-position
arrow returning `Type`, so `P : t → Type`, no fresh universe for
P's binder type itself. -/
inductive EqDep.{u} (t : Sort u) (P : t → Type) (x : t) (p : P x)
    : (y : t) → P y → Prop
  | ReflDep : EqDep t P x p x p

/-! ## 12. Multiple call-site polymorphism — chained polymorphic calls

A def whose body chains multiple polymorphic calls, exercising
the worst case for Lean's universe unifier. -/
noncomputable def chainEq.{u}
    (a : Sort u) (x y z : a)
    (h1 : @Eq.{u} a x y) (h2 : @Eq.{u} a y z) : @Eq.{u} a x z :=
  @Eq.trans.{u} a x y z h1 h2

/-! ## 13. Higher-rank-ish: polymorphic argument used at concrete types

A function that takes a polymorphic-at-Type function and applies
it at two different types. Cryptol prelude shape (`mapPair` at
`Bit` and at `[N]`). The function-typed binder universe locks to
the universe of the types we apply it at.

If we wanted distinct universes for the two applications, we'd
need the function to be rank-2 polymorphic — which the
auto-emit machinery does NOT need to handle. Cryptol pre-
specializes such uses to monomorphic. -/
noncomputable def applyAtTwoTypes
    (f : ∀ (a : Type), a → a) : Bool × Nat :=
  (f Bool false, f Nat 0)

end UniverseStress
