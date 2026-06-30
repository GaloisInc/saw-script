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

theorem bvAdd_wrap_semantics :
    bvAdd 8 (bvNat 8 15) (bvNat 8 1) = bvNat 8 16 := by
  decide

theorem bvSub_wrap_semantics :
    bvSub 8 (bvNat 8 0) (bvNat 8 1) = bvNat 8 255 := by
  decide

theorem bvMul_wrap_semantics :
    bvMul 8 (bvNat 8 16) (bvNat 8 16) = bvNat 8 0 := by
  decide

theorem bvNeg_semantics :
    bvNeg 8 (bvNat 8 1) = bvNat 8 255 := by
  decide

theorem bvShl_semantics :
    bvShl 8 (bvNat 8 0x81) 1 = bvNat 8 0x02 := by
  decide

theorem bvShr_semantics :
    bvShr 8 (bvNat 8 0x81) 1 = bvNat 8 0x40 := by
  decide

theorem bvNot_semantics :
    bvNot 8 (bvNat 8 0x0f) = bvNat 8 0xf0 := by
  decide

theorem bvAnd_semantics :
    bvAnd 8 (bvNat 8 0xf0) (bvNat 8 0xcc) = bvNat 8 0xc0 := by
  decide

theorem bvOr_semantics :
    bvOr 8 (bvNat 8 0xf0) (bvNat 8 0x0f) = bvNat 8 0xff := by
  decide

theorem bvXor_semantics :
    bvXor 8 (bvNat 8 0xaa) (bvNat 8 0xff) = bvNat 8 0x55 := by
  decide

theorem bvult_semantics :
    bvult 8 (bvNat 8 0x01) (bvNat 8 0x02) = true := by
  decide

theorem bvule_semantics :
    bvule 8 (bvNat 8 0x02) (bvNat 8 0x02) = true := by
  decide

theorem bvugt_semantics :
    bvugt 8 (bvNat 8 0x03) (bvNat 8 0x02) = true := by
  decide

theorem bvuge_semantics :
    bvuge 8 (bvNat 8 0x02) (bvNat 8 0x02) = true := by
  decide

theorem bvslt_semantics :
    bvslt 8 (bvNat 8 0xff) (bvNat 8 0x01) = true := by
  decide

theorem bvsle_semantics :
    bvsle 8 (bvNat 8 0xff) (bvNat 8 0xff) = true := by
  decide

theorem bvsgt_semantics :
    bvsgt 8 (bvNat 8 0x01) (bvNat 8 0xff) = true := by
  decide

theorem bvsge_semantics :
    bvsge 8 (bvNat 8 0xff) (bvNat 8 0xff) = true := by
  decide

theorem bvUExt_semantics :
    bvUExt 4 4 (bvNat 4 0x0f) = bvNat 8 0x0f := by
  decide

theorem bvSExt_semantics :
    bvSExt 4 3 (bvNat 4 0x0f) = bvNat 8 0xff := by
  decide

theorem bvPopcount_semantics :
    bvPopcount 8 (bvNat 8 0xf0) = bvNat 8 0x04 := by
  decide

theorem bvCountLeadingZeros_semantics :
    bvCountLeadingZeros 8 (bvNat 8 0x0f) = bvNat 8 0x04 := by
  decide

theorem bvCountTrailingZeros_semantics :
    bvCountTrailingZeros 8 (bvNat 8 0xf0) = bvNat 8 0x04 := by
  decide

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
