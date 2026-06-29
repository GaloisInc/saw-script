import CryptolToLean

open CryptolToLean.SAWCorePreludeExtra

noncomputable section

/-!
Lean half of `drivers/conformance_core`.
-/

theorem lean_id_semantics :
    id (5 : Nat) = 5 := by
  rfl

theorem sawLet_ok_semantics :
    sawLet Nat Bool (Pure.pure 3) (fun x => Pure.pure (x = 3)) =
      Pure.pure true := by
  rfl

theorem sawLet_error_semantics :
    sawLet Nat Bool (Except.error "boom") (fun x => Pure.pure (x = 3)) =
      Except.error "boom" := by
  rfl

end
