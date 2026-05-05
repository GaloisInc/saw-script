/-
Stress-test E1 (tier 1): bvAdd commutativity over [8].

Source: otherTests/saw-core-lean/test_offline_lean_stress.E1_prove0.lean
Cryptol property: \(x y : [8]) -> x + y == y + x

The emitted file defines `goal : Prop`; we import it and discharge.

Baseline: one-line tactic via bvAdd_comm + bvEq_refl.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

theorem goal_closed : goal := by
  intro x y
  rw [bvAdd_comm 8 x y]
  exact bvEq_refl 8 _
