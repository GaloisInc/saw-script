import CryptolToLean

open CryptolToLean.SAWCorePrimitives

noncomputable section

/-!
standalone library-proof row (its former driver twin drivers/conformance_string was retired in the 2026-07-15 restructure; coverage lives in differential/).

The SAW driver proves the same concrete `String` primitive facts with SAW's
`w4` backend and emits the source property for Lean elaboration. This file pins
the corresponding Lean support-library realizations directly.
-/

theorem appendString_semantics :
    equalString (appendString "lean" "-saw") "lean-saw" = true := by
  decide

theorem equalString_distinguishes_values :
    equalString "lean" "saw" = false := by
  decide

end
