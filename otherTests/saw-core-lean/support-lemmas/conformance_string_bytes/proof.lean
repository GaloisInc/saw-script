import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

noncomputable section

/-!
standalone library-proof row (its former driver twin drivers/conformance_string_bytes was retired in the 2026-07-15 restructure; coverage lives in differential/).
-/

theorem bytesToString_hi_semantics :
    equalString (bytesToString 2 #v[bvNat 8 0x48, bvNat 8 0x69]) "Hi" = true := by
  decide

end
