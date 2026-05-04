/-
Stress-test E7 (tier 4): bvAdd associativity at a wide width (256).

Source: otherTests/saw-core-lean/test_offline_lean_stress.E7_prove0.lean
Cryptol property: \(x : [256]) (y : [256]) (z : [256]) ->
                    (x + y) + z == x + (y + z)

The point of this test is that SMT bit-blasting at 256 bits is
painful (cubic-ish in width), while Lean closes the goal in one
line via `bvAdd_assoc`. The discharge is structurally identical
to the width-16 t3 proof — the same `rw [bvAdd_assoc] ; bvEq_refl`
recipe scales because `bvAdd_assoc` is generic in the width.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

theorem goal_closed : goal := by
  intro x y z
  rw [bvAdd_assoc 256 x y z]
  exact bvEq_refl 256 _
