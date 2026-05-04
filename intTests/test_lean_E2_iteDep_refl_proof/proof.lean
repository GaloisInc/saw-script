/-
Stress-test E2 (tier 1): iteDep reflexivity.

Source: otherTests/saw-core-lean/test_offline_lean_stress.saw
Cryptol property: \(b : Bit) (x y : [8]) ->
  (if b then x else y) == (if b then x else y)

Baseline: the two sides are syntactically identical in the
emitted goal, so `bvEq_refl 8 _` closes it without touching
the iteDep wrapper.
-/

import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

noncomputable def goal : Prop :=
  (b : Bool) -> (x : CryptolToLean.SAWCoreVectors.Vec 8 Bool) ->
  (y : CryptolToLean.SAWCoreVectors.Vec 8 Bool) -> @Eq Bool (bvEq 8
  (CryptolToLean.SAWCorePreludeExtra.ite (CryptolToLean.SAWCoreVectors.Vec 8
  Bool) b x y) (CryptolToLean.SAWCorePreludeExtra.ite
  (CryptolToLean.SAWCoreVectors.Vec 8 Bool) b x y)) Bool.true

theorem goal_holds : goal := by
  intro b x y
  exact bvEq_refl 8 _
