/-
Stress-test E5 (tier 3): vector reverse self-inverse over [4][8].

Source: otherTests/saw-core-lean/test_offline_lean_stress.E5_prove0.lean
Cryptol property: \(xs : [4][8]) -> reverse (reverse xs) == xs

The emitted goal has shape:
  foldr-and (gen 4 (fun i => bvEq (at <reverse-reverse-xs> i) xs[i]))
where <reverse-reverse-xs> is the `gen 4 (fun i' => at (gen 4
(fun i'' => at xs (subNat (subNat 4 1) i''))) (subNat (subNat 4
1) i'))` shape.

Discharge:
  1. `gen_atWithDefault_double_reverse` (added to
     SAWCorePreludeProofs to support this and the deferred
     Salsa20 littleendian) collapses the inner double-reverse
     to xs.
  2. Each fold element becomes `bvEq xs[i] xs[i] = true` via
     `bvEq_refl`.
  3. The all-trues fold of size 4 closes by `decide`.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

theorem goal_closed : goal := by
  intro xs
  simp only [gen_atWithDefault_double_reverse]
  have hgen : ∀ i, bvEq 8
      (atWithDefault 4 (CryptolToLean.SAWCoreVectors.Vec 8 Bool)
        (error_unrestricted (CryptolToLean.SAWCoreVectors.Vec 8 Bool) "at: index out of bounds") xs i)
      (atWithDefault 4 (CryptolToLean.SAWCoreVectors.Vec 8 Bool)
        (error_unrestricted (CryptolToLean.SAWCoreVectors.Vec 8 Bool) "at: index out of bounds") xs i)
      = true := fun i => bvEq_refl 8 _
  simp only [hgen]
  decide
