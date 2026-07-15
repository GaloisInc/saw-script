/-
E5: vector reverse is self-inverse over [4][8] (littleendian shape).

Source: workflows/offline_lean_e_series/test_offline_lean_e_series.E5_prove0.lean
Cryptol property: \(xs : [4][8]) -> reverse (reverse xs) == xs

Current proof-carrying emission: reverse indexing goes through
`genWithBoundsM` / `atWithProof_checkedM` with derived indices
`subNat 3 i`. The derived-index bounds evidence does not close by
`assumption`; the completed outline discharges it with `omega`
(`subNat` is reducible `Nat.sub`).

Discharge: unfold the checked helpers; `3 - (3 - i) = i` for `i < 4`
collapses the double reverse; each fold element becomes
`bvEq xs[i] xs[i]`, and the size-4 all-trues fold closes by `rfl`.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

theorem goal_closed : goal := by
  intro xs
  have h_double_rev_idx : ∀ i : Fin 4, 3 - (3 - (i : Nat)) = (i : Nat) := by
    intro i
    omega
  simp [genWithBoundsM, atWithProof_checkedM, foldrM, subNat,
    CryptolToLean.SAWCorePreludeExtra.iteM, h_double_rev_idx, bvEq_refl,
    Pure.pure, Bind.bind, Except.pure, Except.bind]
  rfl
