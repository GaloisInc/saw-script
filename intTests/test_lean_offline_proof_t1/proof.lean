/-
Phase 3b (P3-2): discharge proof for `test_offline_lean.t1_prove0`.

Cryptol property:
    \(x : [8]) (y : [8]) -> x == y ==> x + y == x + x

The goal is provable: when `x == y`, both sides reduce to `bvAdd x x`,
so the equation holds; when `x != y`, the implication is vacuously
true.

This file pins both that the L-16 fix preserves the goal's shape
(see test_offline_lean.t1_prove0.lean.good) AND that the supporting
proof library `CryptolToLean.SAWCoreBitvectors_proofs` is sufficient
to discharge it.
-/

import CryptolToLean
import CryptolToLean.SAWCoreBitvectors_proofs

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeExtra

noncomputable def goal : Prop :=
  (x : CryptolToLean.SAWCoreVectors.Vec 8 Bool) ->
  (y : CryptolToLean.SAWCoreVectors.Vec 8 Bool) -> @Eq Bool
  (CryptolToLean.SAWCorePreludeExtra.ite Bool (bvEq 8 x y) (bvEq 8 (bvAdd 8 x y)
  (bvAdd 8 x x)) Bool.true) Bool.true

theorem goal_holds : goal := by
  intro x y
  -- Unfold the SAW-side ite wrapper. Its body is 'Bool.rec y x b'
  -- — note the swap so SAW's True-first ordering survives. After
  -- unfolding, the goal contains a Lean Bool.rec application that
  -- 'cases' can drive directly.
  unfold CryptolToLean.SAWCorePreludeExtra.ite
  cases hxy : bvEq 8 x y
  · -- bvEq x y = false (the SAW-false case in our wrapper):
    -- Bool.rec returns the first arg post-swap = Bool.true.
    rfl
  · -- bvEq x y = true (the SAW-true case in our wrapper):
    -- Bool.rec returns the consequent = bvEq (x+y) (x+x).
    have hEq : x = y := bvEq_eq_true_imp_eq 8 x y hxy
    rw [hEq]
    exact bvEq_refl 8 _
