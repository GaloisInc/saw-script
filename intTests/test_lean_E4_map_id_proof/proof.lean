/-
Stress-test E4 (tier 2): map of (+0) is identity over [4][32].

Source: otherTests/saw-core-lean/test_offline_lean_stress.saw
Cryptol property: \(xs : [4][32]) -> map (\x -> x + 0) xs == xs

Emitted structure:
  foldr (ite _ _ false) true
    (gen 4 (fun i => bvEq (at (gen 4 (fun i' => bvAdd xs[i'] 0)) i) xs[i]))
  = true

Strategy:
  1. The inner `at (gen ...) i` reduces via atWithDefault_gen.
  2. `bvAdd xs[i] 0 = xs[i]` via bvAdd_id_r.
  3. `bvEq xs[i] xs[i] = true` via bvEq_refl.
  4. The foldr of all-trues collapses by unfolding.

Tries `simp` with those lemmas first.
-/

import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

noncomputable def goal : Prop :=
  (xs : CryptolToLean.SAWCoreVectors.Vec 4 (CryptolToLean.SAWCoreVectors.Vec 32
  Bool)) -> @Eq Bool (foldr Bool Bool 4
  (fun (b1 : Bool) (b2 : Bool) => CryptolToLean.SAWCorePreludeExtra.ite Bool b1
  b2 Bool.false) Bool.true (gen 4 Bool (fun (i : Nat) => bvEq 32 (atWithDefault
  4 (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (error
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) "at: index out of bounds") (gen 4
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (fun (i' : Nat) => bvAdd 32
  (atWithDefault 4 (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (error
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) "at: index out of bounds") xs i')
  (bvNat 32 0))) i) (atWithDefault 4 (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  (error (CryptolToLean.SAWCoreVectors.Vec 32 Bool) "at: index out of bounds")
  xs i)))) Bool.true

theorem goal_holds : goal := by
  intro xs
  simp only [bvAdd_id_r]
  rw [gen_atWithDefault]
  -- Goal: foldr ... (gen 4 (fun i => bvEq xs[i] xs[i])) = true.
  -- Rewrite inner bvEq to true pointwise, then decide.
  have hgen : ∀ i, bvEq 32
      (atWithDefault 4 (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
        (error (CryptolToLean.SAWCoreVectors.Vec 32 Bool) "at: index out of bounds") xs i)
      (atWithDefault 4 (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
        (error (CryptolToLean.SAWCoreVectors.Vec 32 Bool) "at: index out of bounds") xs i)
      = true := fun i => bvEq_refl 32 _
  simp only [hgen]
  decide
