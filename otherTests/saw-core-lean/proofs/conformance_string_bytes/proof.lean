import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

noncomputable section

/-!
Lean half of `drivers/conformance_string_bytes`.
-/

theorem bytesToString_hi_semantics :
    equalString (bytesToString 2 #v[bvNat 8 0x48, bvNat 8 0x69]) "Hi" = true := by
  decide

end
