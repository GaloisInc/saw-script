import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

noncomputable section

/-!
standalone library-proof row (its former driver twin drivers/conformance_vector was retired in the 2026-07-15 restructure; coverage lives in differential/).

The SAW driver proves concrete residual SAWCore vector-helper facts with
SAW's `w4` backend and emits the same source property for Lean elaboration.
This file pins the corresponding Lean support-library realizations directly.
-/

theorem gen_at_semantics :
    atWithDefault 3 Nat 99 (gen 3 Nat (fun i => i + 10)) 2 = 12 := by
  decide

theorem atWithDefault_oob_semantics :
    atWithDefault 3 Nat 99 (gen 3 Nat (fun i => i + 10)) 3 = 99 := by
  decide

theorem shiftL_semantics :
    shiftL 4 Nat 0 #v[1, 2, 3, 4] 1 = #v[2, 3, 4, 0] := by
  decide

theorem shiftR_semantics :
    shiftR 4 Nat 0 #v[1, 2, 3, 4] 1 = #v[0, 1, 2, 3] := by
  decide

theorem rotateL_semantics :
    rotateL 4 Nat #v[1, 2, 3, 4] 1 = #v[2, 3, 4, 1] := by
  decide

theorem rotateR_semantics :
    rotateR 4 Nat #v[1, 2, 3, 4] 1 = #v[4, 1, 2, 3] := by
  decide

theorem foldr_semantics :
    foldr Nat Nat 3 (fun x acc => x + acc) 0 #v[1, 2, 3] = 6 := by
  decide

theorem foldl_semantics :
    foldl Nat Nat 3 (fun acc x => acc + x) 0 #v[1, 2, 3] = 6 := by
  decide

end
