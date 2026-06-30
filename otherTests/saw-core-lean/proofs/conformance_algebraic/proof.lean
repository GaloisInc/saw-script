import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePreludeExtra

noncomputable section

/-!
Lean half of `drivers/conformance_algebraic`.

The SAW driver proves concrete `Either`, unit, empty-record-tail, and `ite`
facts with SAW's `w4` backend. This file pins the corresponding Lean
support-library realizations directly.
-/

theorem either_left_rec_semantics :
    (match (Either.Left 3 : Either Nat Nat) with
     | Either.Left x => x
     | Either.Right y => y) = 3 := by
  rfl

theorem either_right_rec_semantics :
    (match (Either.Right 4 : Either Nat Nat) with
     | Either.Left x => x
     | Either.Right y => y) = 4 := by
  rfl

theorem unit_rec_semantics :
    (match UnitType.Unit with
     | UnitType.Unit => 7) = 7 := by
  rfl

theorem empty_type_rec_semantics :
    (match EmptyType.Empty with
     | EmptyType.Empty => 9) = 9 := by
  rfl

theorem iteM_true_semantics :
    iteM Nat (Pure.pure true) (Pure.pure 1) (Pure.pure 2) = Pure.pure 1 := by
  rfl

theorem iteM_false_semantics :
    iteM Nat (Pure.pure false) (Pure.pure 1) (Pure.pure 2) = Pure.pure 2 := by
  rfl

end
