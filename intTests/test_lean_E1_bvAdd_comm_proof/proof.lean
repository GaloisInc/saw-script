/-
Stress-test E1 (tier 1): bvAdd commutativity over [8].

Source: otherTests/saw-core-lean/test_offline_lean_E1_bvAdd_comm.saw
Cryptol property: \(x y : [8]) -> x + y == y + x

Baseline: should close via `bvAdd_comm 8 x y` + `bvEq_refl 8 _`.
-/

import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

noncomputable def goal : Prop :=
  (x : CryptolToLean.SAWCoreVectors.Vec 8 Bool) ->
  (y : CryptolToLean.SAWCoreVectors.Vec 8 Bool) -> @Eq Bool (bvEq 8 (bvAdd 8 x
  y) (bvAdd 8 y x)) Bool.true

theorem goal_holds : goal := by
  intro x y
  rw [bvAdd_comm 8 x y]
  exact bvEq_refl 8 _
