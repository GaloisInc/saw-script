import Emitted

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

namespace CaseE6

noncomputable def step (bits : CryptolToLean.SAWCoreVectors.Vec 4 Bool) (k : Nat)
    (acc : CryptolToLean.SAWCoreVectors.Vec 3 Bool) :
    CryptolToLean.SAWCoreVectors.Vec 3 Bool :=
  CryptolToLean.SAWCorePreludeExtra.ite _
    (atWithDefault 4 Bool false bits k)
    (bvAdd 3 acc (bvNat 3 1)) acc

end CaseE6

open CaseE6

theorem goal_closed : goal := by
  intro bits
  simp only [Pure.pure, Except.pure, Bind.bind, Except.bind]
  rw [CryptolToLean.SAWCorePreludeProofs.selfRefCompGenFixVecCheckedM_at_zero_eq_natRec_of_bodyAt
    (n := 4)
    (α := CryptolToLean.SAWCoreVectors.Vec 3 Bool)
    (d_at := saw_throw_error (CryptolToLean.SAWCoreVectors.Vec 3 Bool)
      (Except.ok "at: index out of bounds"))
    (d_pair := saw_throw_error
      (PairType Bool (PairType (CryptolToLean.SAWCoreVectors.Vec 3 Bool)
        UnitType)) (Except.ok "at: index out of bounds"))
    (d_fix := saw_unreachable_default (CryptolToLean.SAWCoreVectors.Vec 3 Bool)
      "fix lookup out of bounds")
    (seed := bvNat 3 0)
    (inputsM := Except.ok bits)
    (inputs := bits)
    (stepTrue := fun acc => bvAdd 3 acc (bvNat 3 1))
    (hBodyAt := by rfl)
    (hInputs := rfl)]
  obtain ⟨arr, harr⟩ := bits
  match arr, harr with
  | ⟨[b0, b1, b2, b3]⟩, h =>
    cases h
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
      simp [foldlM, bvEq, bvNat, bvAdd,
        vecToBitVec_bitVecToVec,
        CryptolToLean.SAWCorePreludeExtra.iteM,
        CryptolToLean.SAWCorePreludeExtra.ite,
        atWithDefault, Bind.bind, Pure.pure, Except.bind, Except.pure]
      <;> decide
