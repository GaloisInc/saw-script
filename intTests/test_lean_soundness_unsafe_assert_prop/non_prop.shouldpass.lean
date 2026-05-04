/-
Legitimate uses of `unsafeAssert` the translator actually emits.
These must elaborate cleanly under L-2's `(α : Type)` shape. Each
α below lives in `Type 0` (= SAW's `sort 1`), matching the SAW
primitive's universe.
-/

import CryptolToLean
open CryptolToLean.SAWCorePrimitives

-- All probes are `noncomputable` because `unsafeAssert` is an
-- axiom Lean's code generator refuses to compile.
noncomputable section

-- The dominant translator-emitted shape: a Cryptol size-coercion
-- residual asserting two `Num` values are equal. `Num : Type 0` ✓.
example : @Eq Num (Num.TCNum 4) (Num.TCNum 4) :=
  unsafeAssert Num (Num.TCNum 4) (Num.TCNum 4)

-- At a value-level type (rare but legal under `(α : Type)`).
example : @Eq Bool Bool.true Bool.true :=
  unsafeAssert Bool Bool.true Bool.true

-- At a vector type — what shows up in Cryptol size-coercion
-- residuals over bitvectors.
example (v w : CryptolToLean.SAWCoreVectors.Vec 8 Bool) :
    @Eq (CryptolToLean.SAWCoreVectors.Vec 8 Bool) v w :=
  unsafeAssert _ v w

end
