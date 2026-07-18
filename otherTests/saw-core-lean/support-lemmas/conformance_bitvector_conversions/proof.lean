import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

noncomputable section

/-!
standalone library-proof row (its former driver twin drivers/conformance_bitvector_conversions was retired in the 2026-07-15 restructure; coverage lives in differential/).
-/

theorem bvToNat_semantics :
    equalNat (bvToNat 8 (bvNat 8 0xff)) 255 = true := by
  decide

theorem bvToInt_positive_semantics :
    intEq (bvToInt 8 (bvNat 8 0x7f)) 127 = true := by
  decide

theorem sbvToInt_negative_semantics :
    intEq (sbvToInt 8 (bvNat 8 0xff)) (-1) = true := by
  decide

theorem bvNat_wrap_semantics :
    bvEq 8 (bvNat 8 257) (bvNat 8 0x01) = true := by
  decide

theorem intToBv_negative_semantics :
    bvEq 8 (intToBv 8 (-1)) (bvNat 8 0xff) = true := by
  decide

theorem intToBv_wrap_semantics :
    bvEq 8 (intToBv 8 257) (bvNat 8 0x01) = true := by
  decide

end
