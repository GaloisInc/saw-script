import CryptolToLean

open CryptolToLean.SAWCorePrimitives

noncomputable section

/-!
Lean half of `drivers/conformance_scalar`.

The SAW driver proves the same concrete scalar facts with SAW's `w4` backend
and emits a Lean term for elaboration. This file pins the corresponding Lean
support-library realizations directly.
-/

theorem widthNat_zero_semantics :
    equalNat (widthNat 0) 0 = true := by
  decide

theorem widthNat_power_two_semantics :
    equalNat (widthNat 8) 4 = true := by
  decide

theorem subNat_saturates_semantics :
    equalNat (subNat 3 8) 0 = true := by
  decide

theorem divNat_nonzero_semantics :
    equalNat (divNat 7 2) 3 = true := by
  decide

theorem modNat_nonzero_semantics :
    equalNat (modNat 7 2) 1 = true := by
  decide

theorem intDiv_floor_negative_semantics :
    intEq (intDiv (-3) 2) (-2) = true := by
  decide

theorem intMod_floor_negative_semantics :
    intEq (intMod (-3) 2) 1 = true := by
  decide

theorem intDiv_floor_negative_divisor_semantics :
    intEq (intDiv 3 (-2)) (-2) = true := by
  decide

theorem intMod_floor_negative_divisor_semantics :
    intEq (intMod 3 (-2)) (-1) = true := by
  decide

theorem intMod_repr_semantics :
    intModEq 5 (toIntMod 5 12) (toIntMod 5 2) = true := by
  decide

theorem intMod_add_semantics :
    intModEq 5
      (intModAdd 5 (toIntMod 5 4) (toIntMod 5 4))
      (toIntMod 5 3) = true := by
  decide

theorem intMod_neg_semantics :
    intModEq 5 (intModNeg 5 (toIntMod 5 2)) (toIntMod 5 3) = true := by
  decide

theorem rationalEq_zero_semantics :
    rationalEq 0 0 = true := by
  decide

theorem rationalFloor_zero_semantics :
    intEq (rationalFloor 0) 0 = true := by
  decide

end
