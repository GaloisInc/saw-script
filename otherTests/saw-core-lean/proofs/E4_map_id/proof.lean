/-
E4: map of (+0) is identity over [4][32].

Source: drivers/offline_lean_e_series/test_offline_lean_e_series.E4_prove0.lean
Cryptol property: \(xs : [4][32]) -> map (\x -> x + 0) xs == xs

Current proof-carrying emission: the map and the equality fold both go
through `genWithBoundsM` / `atWithProof_checkedM`, whose embedded
`h_bounds_` evidence closes by `assumption` from the `genWithBoundsM`
binder (no `sorry` fires in the goal statement).

Discharge: unfold the checked helpers, remove the `+0` with
`bvAdd_id_r`, and reduce the size-4 fold of `bvEq xs[i] xs[i]`.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

theorem goal_closed : goal := by
  intro xs
  simp [genWithBoundsM, atWithProof_checkedM, foldrM,
    CryptolToLean.SAWCorePreludeExtra.iteM, bvAdd_id_r, bvEq_refl,
    Pure.pure, Bind.bind, Except.pure, Except.bind]
  rfl
