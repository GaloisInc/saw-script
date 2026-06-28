import Emitted

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

theorem goal_closed : goal := by
  intro xs
  simp only [Pure.pure, Except.pure, Bind.bind, Except.bind]
  rw [CryptolToLean.SAWCorePreludeProofs.selfRefCompGenFixVecCheckedSelfFirstM_at_zero_eq_natRec_of_bodyAt
    (n := 8)
    (β := Vec 32 Bool)
    (α := Vec 32 Bool)
    (d_at := saw_throw_error (Vec 32 Bool)
      (Except.ok "at: index out of bounds"))
    (d_pair := saw_throw_error
      (PairType (Vec 32 Bool) (PairType (Vec 32 Bool) UnitType))
      (Except.ok "at: index out of bounds"))
    (d_fix := saw_unreachable_default (Vec 32 Bool)
      "fix lookup out of bounds")
    (seed := bvNat 32 0)
    (inputsM := Except.ok xs)
    (inputs := xs)
    (step := fun acc x => bvAdd 32 acc x)
    (hBodyAt := by rfl)
    (hInputs := rfl)]
  simp [atWithDefaultM, atWithDefault,
    Bind.bind, Pure.pure, Except.bind, Except.pure]
  change bvEq 32
    (bvAdd 32
      (bvAdd 32
        (bvAdd 32
          (bvAdd 32
            (bvAdd 32
              (bvAdd 32
                (bvAdd 32
                  (bvAdd 32 (bvNat 32 0) xs[0])
                  xs[1])
                xs[2])
              xs[3])
            xs[4])
          xs[5])
        xs[6])
      xs[7])
    (bvAdd 32
      (bvAdd 32
        (bvAdd 32
          (bvAdd 32
            (bvAdd 32
              (bvAdd 32
                (bvAdd 32 xs[0] xs[1])
                xs[2])
              xs[3])
            xs[4])
          xs[5])
        xs[6])
      xs[7]) = true
  rw [bvAdd_id_l]
  exact bvEq_refl 32 _
