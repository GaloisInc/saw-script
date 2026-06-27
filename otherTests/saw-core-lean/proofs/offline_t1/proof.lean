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
  by_cases hxy : bvEq 8 x y = true
  · have hEq : x = y := bvEq_eq_true_imp_eq 8 x y hxy
    subst y
    simp [CryptolToLean.SAWCorePreludeExtra.iteM, bvEq_refl, Pure.pure,
      Bind.bind, Except.pure, Except.bind]
  · have hfalse : bvEq 8 x y = false := by
      cases h : bvEq 8 x y
      · rfl
      · exfalso
        exact hxy h
    simp [CryptolToLean.SAWCorePreludeExtra.iteM, hfalse, Pure.pure,
      Bind.bind, Except.pure, Except.bind]
