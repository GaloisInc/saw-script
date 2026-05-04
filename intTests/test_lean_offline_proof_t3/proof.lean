/-
Discharge proof for test_offline_lean.t3_prove0.

Cryptol property: \(x : [16]) (y : [16]) (z : [16]) ->
                    (x + y) + z == x + (y + z).

Direct application of bvAdd_assoc, then bvEq_refl.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

theorem goal_closed : goal := by
  intro x y z
  rw [bvAdd_assoc 16 x y z]
  exact bvEq_refl 16 _
