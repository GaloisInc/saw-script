/-
Legitimate uses of `coerce` at the translator-emitted shape.
Each α, β here is at `Type` (= Type 0 = SAW's sort 0). MUST
elaborate cleanly.
-/

import CryptolToLean
open CryptolToLean.SAWCorePrimitives

noncomputable section

-- The general shape: type-level transport across Eq Type.
example (α β : Type) (eq : @Eq Type α β) (x : α) : β :=
  coerce α β eq x

-- Concrete instantiation (the translator emits coerce on Num,
-- Vec n α, etc. in size-coercion residuals).
example (eq : @Eq Type Num Num) (x : Num) : Num :=
  coerce Num Num eq x

example (eq : @Eq Type (CryptolToLean.SAWCoreVectors.Vec 8 Bool)
                       (CryptolToLean.SAWCoreVectors.Vec 8 Bool))
        (v : CryptolToLean.SAWCoreVectors.Vec 8 Bool) :
        CryptolToLean.SAWCoreVectors.Vec 8 Bool :=
  coerce _ _ eq v

end
