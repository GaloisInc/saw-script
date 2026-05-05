/-
"Attack" pattern: try to use `coerce` at a higher universe than
SAW's `sort 0` (= Lean's `Type 0` = `Type`). SAW's primitive is
fixed at `sort 0`; a Lean stand-in that admits `Type 1` or higher
is *broader than SAW* — even though no translator-emitted code
reaches that surface, the asymmetry violates faithful
transposition.

If `coerce` ever drifts to a broader universe, this attack will
elaborate and the regression test will fail loud.
-/

import CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePrimitives

-- α and β at Type 1. The axiom expects α, β : Type (= Type 0).
-- Lean must reject because Type 1 : Type 2, not Type 0.
example (α β : Type 1) (eq : @Eq (Type 1) α β) (x : α) : β :=
  coerce α β eq x
