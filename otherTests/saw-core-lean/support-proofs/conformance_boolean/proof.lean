import CryptolToLean

open CryptolToLean.SAWCorePreludeExtra

noncomputable section

/-!
standalone library-proof row (its former driver twin drivers/conformance_boolean was retired in the 2026-07-15 restructure; coverage lives in differential/).

The SAW driver proves concrete Boolean facts with SAW's `w4` backend and emits
the same source property for Lean elaboration. This file pins the checked
Lean-side facades for the Prelude Boolean definitions that are not just Lean
core Boolean connectives.
-/

theorem lean_bool_connective_smoke :
    (!false && true && (false || true)) = true := by
  decide

theorem xor_true_false_semantics :
    xor (Pure.pure true) (Pure.pure false) = Pure.pure true := by
  rfl

theorem xor_false_true_semantics :
    xor (Pure.pure false) (Pure.pure true) = Pure.pure true := by
  rfl

theorem boolEq_true_true_semantics :
    boolEq (Pure.pure true) (Pure.pure true) = Pure.pure true := by
  rfl

theorem boolEq_true_false_semantics :
    boolEq (Pure.pure true) (Pure.pure false) = Pure.pure false := by
  rfl

theorem boolEq_false_false_semantics :
    boolEq (Pure.pure false) (Pure.pure false) = Pure.pure true := by
  rfl

end
