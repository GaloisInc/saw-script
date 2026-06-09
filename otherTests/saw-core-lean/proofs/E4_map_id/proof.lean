/-
Stress-test E4 (tier 2): map of (+0) is identity over [4][32].

Source: otherTests/saw-core-lean/test_offline_lean_stress.E4_prove0.lean
Cryptol property: \(xs : [4][32]) -> map (\x -> x + 0) xs == xs

Discharge:
  1. simp only [bvAdd_id_r] — remove the `+0`.
  2. rw [gen_atWithDefault] — gen-after-at round-trip collapses.
  3. hgen : pointwise bvEq xs[i] xs[i] = true (simp can't generate
     this from bvEq_refl alone because of the metavariable in RHS).
  4. simp only [hgen]; decide — fold of all-trues at size 4.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

theorem goal_closed : goal := by
  intro xs
  simp only [bvAdd_id_r]
  rw [gen_atWithDefault]
  have hgen : ∀ i, bvEq 32
      (atWithDefault 4 (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
        (error_unrestricted (CryptolToLean.SAWCoreVectors.Vec 32 Bool) "at: index out of bounds") xs i)
      (atWithDefault 4 (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
        (error_unrestricted (CryptolToLean.SAWCoreVectors.Vec 32 Bool) "at: index out of bounds") xs i)
      = true := fun i => bvEq_refl 32 _
  simp only [hgen]
  decide
