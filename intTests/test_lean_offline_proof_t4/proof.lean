/-
Phase 3b (P3-2): discharge proof for `test_offline_lean.t4_prove0`.

Cryptol property:
    \(b : Bit) (x : [8]) (y : [8]) -> (if b then x else y) == (if ~b then y else x)

Pure Bool case-symmetry. Proof: case-split on b, both sides reduce
to the same value.
-/

import CryptolToLean
import CryptolToLean.SAWCoreBitvectors_proofs

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

noncomputable def goal : Prop :=
  (b : Bool) -> (x : CryptolToLean.SAWCoreVectors.Vec 8 Bool) ->
  (y : CryptolToLean.SAWCoreVectors.Vec 8 Bool) -> @Eq Bool (bvEq 8
  (CryptolToLean.SAWCorePreludeExtra.ite (CryptolToLean.SAWCoreVectors.Vec 8
  Bool) b x y) (CryptolToLean.SAWCorePreludeExtra.ite
  (CryptolToLean.SAWCoreVectors.Vec 8 Bool)
  (CryptolToLean.SAWCorePreludeExtra.ite Bool b Bool.false Bool.true) y x))
  Bool.true

theorem goal_holds : goal := by
  intro b x y
  -- Unfold our handwritten ite wrappers; the goal becomes a
  -- chain of Bool.rec calls that 'cases b' drives concretely.
  unfold CryptolToLean.SAWCorePreludeExtra.ite
  cases b
  · -- b = false: lhs = y, rhs = ite (ite b f t) y x = ite true y x = y.
    -- bvEq y y = true.
    exact bvEq_refl 8 _
  · -- b = true: lhs = x, rhs = ite (ite b f t) y x = ite false y x = x.
    -- bvEq x x = true.
    exact bvEq_refl 8 _
