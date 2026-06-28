import Emitted

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs
open CryptolToLean.SAWCorePreludeExtra

/- Width-32 popcount discharge for the current checked wrapped
recurrence emission.  The proof first bridges the generated
`genFixVecChecked` body to a `Nat.rec`, then proves the emitted
`foldlM` succeeds and bridges it to the matching pure `foldl`. -/
theorem goal_closed : goal := by
  intro bits
  simp only [Pure.pure, Except.pure]
  rw [CryptolToLean.SAWCorePreludeProofs.selfRefCompGenFixVecCheckedM_at_zero_eq_natRec_of_bodyAt
    (n := 32)
    (α := Vec 32 Bool)
    (d_at := saw_throw_error (Vec 32 Bool)
      (Except.ok "at: index out of bounds"))
    (d_pair := saw_throw_error
      (PairType Bool (PairType (Vec 32 Bool) UnitType))
      (Except.ok "at: index out of bounds"))
    (d_fix := saw_unreachable_default (Vec 32 Bool)
      "fix lookup out of bounds")
    (seed := bvNat 32 0)
    (inputsM := Except.ok bits)
    (inputs := bits)
    (stepTrue := fun acc => bvAdd 32 acc (bvNat 32 1))
    (hBodyAt := by rfl)
    (hInputs := rfl)]
  have hFold := foldlM_pure_eq_foldl Bool (Vec 32 Bool) 32
    (fun acc b => iteM (Vec 32 Bool) b
      (Bind.bind acc (fun v_1 => Bind.bind (Except.ok (bvNat 32 1))
        (fun v_2 => Except.ok (bvAdd 32 v_1 v_2))))
      acc)
    (fun acc b => CryptolToLean.SAWCorePreludeExtra.ite (Vec 32 Bool) b
      (bvAdd 32 acc (bvNat 32 1)) acc)
      (bvNat 32 0) bits (by
      intro acc b
      cases b <;> simp [iteM, CryptolToLean.SAWCorePreludeExtra.ite,
        Bind.bind, Except.bind])
  generalize hResult :
    foldlM Bool (Vec 32 Bool) 32
      (fun acc b => iteM (Vec 32 Bool) b
        (Bind.bind acc (fun v_1 => Bind.bind (Except.ok (bvNat 32 1))
          (fun v_2 => Except.ok (bvAdd 32 v_1 v_2))))
        acc)
      (Except.ok (bvNat 32 0)) (Except.ok bits) = result
  have hResultOk :
      result = Except.ok
        (foldl Bool (Vec 32 Bool) 32
          (fun acc b => CryptolToLean.SAWCorePreludeExtra.ite (Vec 32 Bool) b
            (bvAdd 32 acc (bvNat 32 1)) acc)
          (bvNat 32 0) bits) := by
    rw [← hResult]
    exact hFold
  cases result with
  | error err => cases hResultOk
  | ok folded =>
      cases hResultOk
      rw [foldl_eq_natRec_atWithDefault Bool (Vec 32 Bool) 32
        (fun acc b => CryptolToLean.SAWCorePreludeExtra.ite (Vec 32 Bool) b
          (bvAdd 32 acc (bvNat 32 1)) acc)
        (bvNat 32 0) bits false]
      exact congrArg Except.ok (bvEq_refl 32 _)
