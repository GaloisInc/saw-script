import CryptolToLean

open CryptolToLean.SAWCorePreludeExtra

noncomputable section

/-!
standalone library-proof row (its former driver twin drivers/conformance_core was retired in the 2026-07-15 restructure; coverage lives in differential/).
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
