import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

local notation "Bv8" => CryptolToLean.SAWCoreVectors.Vec 8 Bool
local notation "VecBv8" => CryptolToLean.SAWCoreVectors.Vec 4 Bv8

/-! Bool-fold-of-true characterisation for Fin 4. Vector.foldr of the
&&-style fold over a Vector.ofFn whose body is uniformly `true` is `true`. -/
private theorem foldr_and_ofFn_4_eq_true (f : Fin 4 → Bool)
    (h : ∀ i : Fin 4, f i = true) :
    Vector.foldr (fun b1 b2 => Bool.rec false b2 b1) true (Vector.ofFn f) = true := by
  -- Make all 4 hypotheses concrete.
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  have h3 := h ⟨3, by decide⟩
  -- Strategy: rewrite to v[0] = f 0, etc., then Vector.foldr ⟨[t,t,t,t]⟩ true = true.
  -- Use Vector.foldr's relationship to recursion via getElem.
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

theorem goal_closed : goal := by
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
