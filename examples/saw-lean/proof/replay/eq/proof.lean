/-
Replay discharge for impl_eq_spec (demo.saw step 5): SAW re-emits the goal
fresh, stages this file against it, and admits the goal on Lean's
kernel authority via the factored trust kernel
(saw-core-lean/replay/lean-check-core.sh). Same tactic as
proof/Proofs/Eq.lean — top-level (unnamespaced) goal_closed, per
the replay closer contract.
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
  have hfin0 : ((0 : Fin 4) : Nat) = 0 := rfl
  have hfin1 : ((1 : Fin 4) : Nat) = 1 := rfl
  have hfin2 : ((2 : Fin 4) : Nat) = 2 := rfl
  have hfin3 : ((3 : Fin 4) : Nat) = 3 := rfl
  simp +decide [genWithBoundsM, atWithProof_checkedM, atRuntimeCheckedM,
    foldrM, subNat, vecSequenceM, Vector.ofFnM_succ, Vector.ofFnM_zero,
    intLe, intSub, intNeg, intToNat, natToInt,
    hfin0, hfin1, hfin2, hfin3,
    CryptolToLean.SAWCorePreludeExtra.iteM, h_double_rev_idx, bvEq_refl,
    Pure.pure, Bind.bind, Except.pure, Except.bind]
