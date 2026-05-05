/-
Discharge proof for test_offline_lean.t1_prove0.

Cryptol property: \(x : [8]) (y : [8]) -> x == y ==> x + y == x + x

Provable because when x == y both sides reduce to `bvAdd x x`; when
x != y the implication is vacuously true.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

theorem goal_closed : goal := by
  intro x y
  -- Unfold the SAW ite wrapper. The body is Bool.rec y x b — note
  -- the swap, so SAW's True-first ordering survives. After
  -- unfolding, `cases` can drive through the resulting Bool.rec.
  unfold CryptolToLean.SAWCorePreludeExtra.ite
  cases hxy : bvEq 8 x y
  · rfl
  · have hEq : x = y := bvEq_eq_true_imp_eq 8 x y hxy
    rw [hEq]
    exact bvEq_refl 8 _
