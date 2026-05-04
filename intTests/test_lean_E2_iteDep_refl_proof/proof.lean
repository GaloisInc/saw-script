/-
Stress-test E2 (tier 1): iteDep reflexivity.

Source: otherTests/saw-core-lean/test_offline_lean_stress.E2_prove0.lean
Cryptol property: \(b : Bit) (x y : [8]) ->
  (if b then x else y) == (if b then x else y)

Both sides of the emitted goal are identical, so bvEq_refl closes
immediately without touching the iteDep wrapper.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

theorem goal_closed : goal := by
  intro b x y
  exact bvEq_refl 8 _
