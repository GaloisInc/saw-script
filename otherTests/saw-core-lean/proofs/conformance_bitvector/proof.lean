import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

noncomputable section

/-!
Lean half of `drivers/conformance_bitvector`.

The SAW driver proves the same concrete properties with SAW's `w4` backend and
emits a Lean term for elaboration. This file pins the corresponding Lean
support-library realizations directly, avoiding generated-literal normalization
cost while still making SAW-vs-Lean drift visible in the paired test.
-/

theorem bvUDiv_nonzero_semantics :
    bvUDiv 8 (bvNat 8 13) (bvNat 8 3) = bvNat 8 4 := by
  decide

theorem bvURem_nonzero_semantics :
    bvURem 8 (bvNat 8 13) (bvNat 8 3) = bvNat 8 1 := by
  decide

theorem bvSDiv_nonzero_negative_semantics :
    bvSDiv 7 (intToBv 8 (-7)) (intToBv 8 2) = intToBv 8 (-3) := by
  decide

theorem bvSRem_nonzero_negative_semantics :
    bvSRem 7 (intToBv 8 (-7)) (intToBv 8 2) = intToBv 8 (-1) := by
  decide

theorem bvSShr_negative_semantics :
    bvSShr 7 (intToBv 8 (-8)) 1 = intToBv 8 (-4) := by
  decide

theorem bvLg2_zero_semantics :
    bvLg2 8 (bvNat 8 0) = bvNat 8 0 := by
  decide

theorem bvLg2_one_semantics :
    bvLg2 8 (bvNat 8 1) = bvNat 8 0 := by
  decide

theorem bvLg2_non_power_two_semantics :
    bvLg2 8 (bvNat 8 3) = bvNat 8 2 := by
  decide

theorem bvLg2_power_two_semantics :
    bvLg2 8 (bvNat 8 4) = bvNat 8 2 := by
  decide

theorem bvLg2_next_non_power_two_semantics :
    bvLg2 8 (bvNat 8 5) = bvNat 8 3 := by
  decide

end
