/-
Legitimate uses of `error` the translator actually emits. These
must elaborate cleanly even with the Stage-4.2 Sort (u+1)
restriction in place.
-/

import CryptolToLean
open CryptolToLean.SAWCorePrimitives

-- All probes are `noncomputable` because `error` is an axiom Lean's
-- code generator refuses to compile — same reason every translated
-- def is emitted as `noncomputable def`.
noncomputable section

-- error at a value-level type (the common case in normalized
-- Cryptol output: out-of-bounds indices, unreachable Num.rec
-- branches at finite Nums).
example : Bool := error Bool "unreachable"

example : CryptolToLean.SAWCoreVectors.Vec 8 Bool :=
  error _ "unreachable"

-- error at a function type (Stream-shaped TCInf branch).
example : (a : Type) → Stream a → Stream a :=
  error _ "Unexpected Fin constraint violation!"

end
