import CryptolToLean

open CryptolToLean.SAWCorePreludeExtra
open CryptolToLean.SAWCorePrimitives

noncomputable section

/-!
Lean half of `drivers/conformance_error`.

The driver checks SAW source semantics for unreachable Cryptol `error`
branches. These theorems pin the checked `Except.error` helper and `iteM`
branch behavior directly.
-/

theorem saw_throw_error_semantics :
    saw_throw_error Nat (Pure.pure "boom") = Except.error "boom" := by
  rfl

theorem iteM_true_ignores_error_branch :
    iteM Nat (Pure.pure true) (Pure.pure 1)
      (saw_throw_error Nat (Pure.pure "boom")) = Pure.pure 1 := by
  rfl

theorem iteM_false_ignores_error_branch :
    iteM Nat (Pure.pure false) (saw_throw_error Nat (Pure.pure "boom"))
      (Pure.pure 2) = Pure.pure 2 := by
  rfl

end
