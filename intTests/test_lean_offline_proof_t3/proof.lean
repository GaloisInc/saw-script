/-
Phase 3b (P3-2): discharge proof for `test_offline_lean.t3_prove0`.

Cryptol property:
    \(x : [16]) (y : [16]) (z : [16]) -> (x + y) + z == x + (y + z)

bvAdd associativity, lifted directly via the bvAdd_assoc axiom in
CryptolToLean.SAWCoreBitvectors_proofs.
-/

import CryptolToLean
import CryptolToLean.SAWCoreBitvectors_proofs

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

noncomputable def goal : Prop :=
  (x : CryptolToLean.SAWCoreVectors.Vec 16 Bool) ->
  (y : CryptolToLean.SAWCoreVectors.Vec 16 Bool) ->
  (z : CryptolToLean.SAWCoreVectors.Vec 16 Bool) -> @Eq Bool (bvEq 16 (bvAdd 16
  (bvAdd 16 x y) z) (bvAdd 16 x (bvAdd 16 y z))) Bool.true

theorem goal_holds : goal := by
  intro x y z
  rw [bvAdd_assoc 16 x y z]
  exact bvEq_refl 16 _
