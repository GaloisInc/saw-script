import CryptolToLean

open CryptolToLean.SAWCorePrimitives

noncomputable section

/-!
standalone library-proof row (its former driver twin drivers/conformance_scalar_extra was retired in the 2026-07-15 restructure; coverage lives in differential/).

These theorems pin scalar support-library realizations that are not covered by
the older division-focused scalar conformance fixture.
-/

theorem addNat_semantics :
    equalNat (addNat 4 5) 9 = true := by
  decide

theorem mulNat_semantics :
    equalNat (mulNat 6 7) 42 = true := by
  decide

theorem minNat_semantics :
    equalNat (minNat 3 8) 3 = true := by
  decide

theorem maxNat_semantics :
    equalNat (maxNat 3 8) 8 = true := by
  decide

theorem expNat_semantics :
    equalNat (expNat 2 5) 32 = true := by
  decide

theorem doubleNat_semantics :
    equalNat (doubleNat 6) 12 = true := by
  decide

theorem pred_zero_semantics :
    equalNat (pred 0) 0 = true := by
  decide

theorem pred_succ_semantics :
    equalNat (pred 9) 8 = true := by
  decide

theorem ltNat_semantics :
    ltNat 3 4 = true := by
  decide

theorem intAdd_semantics :
    intEq (intAdd (-2) 5) 3 = true := by
  decide

theorem intSub_semantics :
    intEq (intSub 2 5) (-3) = true := by
  decide

theorem intMul_semantics :
    intEq (intMul (-3) 4) (-12) = true := by
  decide

theorem intLe_semantics :
    intLe (-3) 2 = true := by
  decide

theorem intLt_semantics :
    intLt (-3) 2 = true := by
  decide

theorem intToNat_negative_semantics :
    equalNat (intToNat (-3)) 0 = true := by
  decide

theorem intToNat_positive_semantics :
    equalNat (intToNat 7) 7 = true := by
  decide

theorem fromIntMod_semantics :
    intEq (fromIntMod 5 (toIntMod 5 12)) 2 = true := by
  decide

theorem intModSub_semantics :
    intModEq 5
      (intModSub 5 (toIntMod 5 1) (toIntMod 5 3))
      (toIntMod 5 3) = true := by
  decide

theorem intModMul_semantics :
    intModEq 5
      (intModMul 5 (toIntMod 5 3) (toIntMod 5 4))
      (toIntMod 5 2) = true := by
  decide

end
