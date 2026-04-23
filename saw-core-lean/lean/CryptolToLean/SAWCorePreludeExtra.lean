/-
`CryptolToLean.SAWCorePreludeExtra` — handwritten Lean realisations
for SAWCore Prelude constants whose auto-translation would be
semantically wrong or can't elaborate.

Each definition here is paired with a `mapsTo` entry in
`SAWCoreLean.SpecialTreatment.sawCorePreludeSpecialTreatmentMap`
that routes the SAWCore name to its realisation here.

**Soundness discipline.** Every realisation in this file must be
semantically equivalent to the SAWCore source it replaces. If in
doubt, prove the equivalence. See `doc/2026-04-22_soundness.md` for
the rule.
-/

namespace CryptolToLean.SAWCorePreludeExtra

/-
## Bool elimination

SAWCore declares `data Bool { True; False; }` — True first. The
auto-generated `Bool#rec1` thus takes `(motive, trueCase, falseCase,
scrutinee)`. Lean's `Bool.rec` takes `(motive, falseCase, trueCase,
scrutinee)` — constructor order swapped.

A faithful translation of SAWCore's `iteDep` / `ite` must permute
the case arguments; otherwise every elimination silently swaps the
True and False branches. Realise them here with the correct
permutation. The `rfl` proofs below verify that the reduction
behaviour matches the SAWCore `iteDep_True` / `iteDep_False` axioms.
-/

/-- `iteDep p b fT fF = p b`, matching SAWCore's argument order
(True case before False case). -/
@[reducible] noncomputable def iteDep
    (p : Bool → Type) (b : Bool) (fT : p true) (fF : p false) : p b :=
  Bool.rec fF fT b

/-- SAWCore's reduction rule: `iteDep p True fT fF = fT`. -/
theorem iteDep_True (p : Bool → Type) (fT : p true) (fF : p false) :
    iteDep p true fT fF = fT := rfl

/-- SAWCore's reduction rule: `iteDep p False fT fF = fF`. -/
theorem iteDep_False (p : Bool → Type) (fT : p true) (fF : p false) :
    iteDep p false fT fF = fF := rfl

/-- Non-dependent SAWCore `ite : (a : sort 1) -> Bool -> a -> a -> a`,
matching SAWCore's argument order: True case before False case. -/
@[reducible] noncomputable def ite (a : Type) (b : Bool) (x y : a) : a :=
  Bool.rec y x b

/-- `ite` agrees with the non-dependent instantiation of `iteDep`. -/
theorem ite_eq_iteDep (a : Type) (b : Bool) (x y : a) :
    ite a b x y = iteDep (fun _ => a) b x y := rfl

end CryptolToLean.SAWCorePreludeExtra
