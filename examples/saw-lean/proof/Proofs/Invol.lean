-- Discharge for `revInvolutive` (rev.cry / demo.saw).
-- `Proofs/InvolEmitted.lean` is a verbatim copy of the
-- `offline_lean`-emitted file (`out/invol_prove0.lean`) and
-- defines `goal : Prop := (xs : [4][8]) -> reverse (reverse xs) == xs`.
-- The theorem below closes that goal.
import Proofs.InvolEmitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

/-! Bool-fold-of-true characterisation for Fin 4. Vector.foldr of the
&&-style fold over a Vector.ofFn whose body is uniformly `true` is `true`. -/
private theorem foldr_and_ofFn_4_eq_true (f : Fin 4 → Bool)
    (h : ∀ i : Fin 4, f i = true) :
    Vector.foldr (fun b1 b2 => Bool.rec false b2 b1) true (Vector.ofFn f) = true := by
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  have h3 := h ⟨3, by decide⟩
  have heq : Vector.ofFn f = (Vector.ofFn (fun _ : Fin 4 => true) : Vector Bool 4) := by
    apply Vector.ext
    intro k hk
    simp only [Vector.getElem_ofFn]
    match k, hk with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
  rw [heq]
  rfl

theorem invol_goal_closed : InvolDemo.goal := by
  unfold InvolDemo.goal
  intro xs
  unfold coerce
  simp only [cast_eq]
  simp only [gen, atWithDefault, foldr]
  apply foldr_and_ofFn_4_eq_true
  intro i
  -- Per-index reasoning: for i ∈ {0,1,2,3}, the body reduces to
  -- bvEq 8 xs[k] xs[k] = true for some k.
  match i with
  | ⟨0, _⟩ =>
      simp only [Vector.getElem_ofFn, Fin.val_mk, addNat, intSub, intLe, natToInt,
                 intToNat, intNeg, CryptolToLean.SAWCorePreludeExtra.ite,
                 Either.rec]
      exact bvEq_refl 8 _
  | ⟨1, _⟩ =>
      simp only [Vector.getElem_ofFn, Fin.val_mk, addNat, intSub, intLe, natToInt,
                 intToNat, intNeg, CryptolToLean.SAWCorePreludeExtra.ite,
                 Either.rec]
      exact bvEq_refl 8 _
  | ⟨2, _⟩ =>
      simp only [Vector.getElem_ofFn, Fin.val_mk, addNat, intSub, intLe, natToInt,
                 intToNat, intNeg, CryptolToLean.SAWCorePreludeExtra.ite,
                 Either.rec]
      exact bvEq_refl 8 _
  | ⟨3, _⟩ =>
      simp only [Vector.getElem_ofFn, Fin.val_mk, addNat, intSub, intLe, natToInt,
                 intToNat, intNeg, CryptolToLean.SAWCorePreludeExtra.ite,
                 Either.rec]
      exact bvEq_refl 8 _
