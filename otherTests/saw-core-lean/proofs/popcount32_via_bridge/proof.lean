/-
Width-32 popcount discharge via two parametric bridges in the
proofs library:

  - `saw_self_ref_comp_iterate` rewrites the SAW emission's outer
    `atWithDefault/gen/genFix/zip` chain into a `Nat.rec` form.
  - `foldl_eq_natRec_atWithDefault` rewrites Vector.foldl into
    the matching `Nat.rec` form.

After both rewrites apply, the two sides of the goal are
syntactically identical `Nat.rec` expressions over the same 32
booleans, modulo the (`@[reducible]`) `Popcount32.step`
unfolding — closure is by definitional equality.

Both bridges are parametric in n, so the same template closes
ChaCha20 round-folding (n = 10) and any other `BoundedVecFold`-
shape Cryptol comprehension.
-/

import Emitted

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs
open CryptolToLean.SAWCorePreludeExtra

namespace Popcount32

/-- Per-step accumulator: `if bit then bvAdd 32 acc 1 else acc`.
Reducible so it folds away during defeq-check when applying the
parametric bridge (whose body has `step bit acc` and the SAW
emission has the inline `ite` form). -/
@[reducible] noncomputable def step (b : Bool) (acc : Vec 32 Bool) : Vec 32 Bool :=
  ite _ b (bvAdd 32 acc (bvNat 32 1)) acc

end Popcount32

theorem goal_closed : goal := by
  intro bits
  refine eq_imp_bvEq_eq_true 32 _ _ ?_
  -- Bridge the SAW emission's RHS (self-referential comprehension shape)
  -- to a Nat.rec form. Three error_unrestricted defaults match what the
  -- emission supplies; β-reduction (`(fun ic => …) (gen 33 _ lookup_)`),
  -- numeric defeq (`32+1 = 33`, `Nat.min 32 33 = 32`), and `Popcount32.step`
  -- unfolding are handled during defeq checking — none triggers
  -- `Vector.ofFn` materialization.
  refine Eq.trans ?_ (saw_self_ref_comp_iterate 32 (Vec 32 Bool)
        (error_unrestricted (Vec 32 Bool) "at: index out of bounds")
        (error_unrestricted (Vec 32 Bool) "fix lookup out of bounds")
        (error_unrestricted (PairType Bool (PairType (Vec 32 Bool) UnitType))
          "at: index out of bounds")
        (bvNat 32 0) bits Popcount32.step).symm
  -- Bridge the LHS's `foldl` form to the matching Nat.rec form. After
  -- this both sides are syntactically equal Nat.rec expressions
  -- (modulo `Popcount32.step` unfolding, which is `@[reducible]`).
  rw [foldl_eq_natRec_atWithDefault Bool (Vec 32 Bool) 32
        (fun acc b => ite _ b (bvAdd 32 acc (bvNat 32 1)) acc)
        (bvNat 32 0) bits false]
