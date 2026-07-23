/-
LLVM popcount (Hacker's Delight SWAR) vs the Cryptol popCount
self-referential comprehension — completed outline, ACCEPTED under the
`native-eval` trust tier (see .trust-tier).

Two halves:
  * the SPEC side is the R2 fix-recognizer shape; the PCDischarge
    namespace (copied from proofs/offline_lean_popcount32 — the
    emitted fix bodies are alpha-identical) replaces the emitted
    productivity placeholder with the proved pc_h_prod and collapses
    the bounded-fix choose to the closed-form pcSol / pcChain;
  * the LLVM side is genuine 32-bit SWAR bit-twiddling; the residual
    `bvEq 32 (swar x) (pcChain x 32)` is a real SWAR-popcount
    correctness theorem, closed by `bv_decide` with the bit accesses
    bridged onto the SAME BitVec atom via getMsbD_vecToBitVec_lt.

TRUST TIER NOTE — RESOLVE LATER: `bv_decide` depends on
per-invocation proof-local native axioms; see the two-tier policy in
saw-core-lean/doc/proof-cookbook.md. RESOLUTION TRIGGER (recorded in
TODO.md): when lean-smt's cvc5 BV proof reconstruction lands upstream,
swap `bv_decide` -> `smt` and delete .trust-tier.
-/
import CryptolToLean
import Std.Tactic.BVDecide

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

namespace PCDischarge

/-- The translated popcount fix body, verbatim from the emitted
artifact (vacuous fallback branches stripped; every bound closes by
omega), parameterized over the wrapped input bit vector. -/
@[reducible] noncomputable def pcBody (bits : Except String (Vec 32 Bool)) :
    Except String (Vec 33 (Vec 32 Bool)) →
      Except String (Vec 33 (Vec 32 Bool)) :=
  (fun (ic : Except String (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool))) => genWithBoundsM
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool)
  (fun (i' : Nat) (h_gen_bounds_ : LT.lt i'
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))) => CryptolToLean.SAWCorePreludeExtra.iteM
  (Vec (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) (Pure.pure (ltNat i'
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  CryptolToLean.SAWCorePrimitives.one_macro))) (atRuntimeCheckedM
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  CryptolToLean.SAWCorePrimitives.one_macro) (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) (vecSequenceM 1 (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) #v[Pure.pure (bvNat
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))
  CryptolToLean.SAWCorePrimitives.zero_macro)]) i')
  (let h_bounds_obligation_ : (Prop) := (LT.lt (subNat i'
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  CryptolToLean.SAWCorePrimitives.one_macro))
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))));
  let h_bounds_ : (h_bounds_obligation_) := ((by (try unfold h_bounds_obligation_); (first | assumption | omega | (simp only [natPos_macro, bit0_macro, bit1_macro, one_macro, zero_macro, succ_macro, subNat, addNat, mulNat, minNat, maxNat, divNat_eq_div, modNat_eq_mod, divNat_checked_eq_div, modNat_checked_eq_mod, Nat.sub_eq, Nat.add_eq, Nat.mul_eq] at *; omega) | skip)));
  atWithProof_checkedM (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) (genWithBoundsM
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool)
  (fun (i'' : Nat) (h_gen_bounds_ : LT.lt i''
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))) => let x__ := (let h_bounds_obligation_ : (Prop) := (LT.lt
  i'' (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))));
  let h_bounds_ : (h_bounds_obligation_) := ((by (try unfold h_bounds_obligation_); (first | assumption | omega | (simp only [natPos_macro, bit0_macro, bit1_macro, one_macro, zero_macro, succ_macro, subNat, addNat, mulNat, minNat, maxNat, divNat_eq_div, modNat_eq_mod, divNat_checked_eq_div, modNat_checked_eq_mod, Nat.sub_eq, Nat.add_eq, Nat.mul_eq] at *; omega) | skip)));
  atWithProof_checkedM (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) (PairType Bool (PairType (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) UnitType)) (Bind.bind
  bits (fun v_4 => Bind.bind ic (fun v_5 => Pure.pure (zip Bool (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool)
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_4 v_5)))) i'' h_bounds_);
  let x__' := (Bind.bind (Bind.bind x__ (fun v_2 => Pure.pure (Pair_snd Bool
  (PairType (Vec (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) UnitType) v_2)))
  (fun v_2' => Pure.pure (Pair_fst (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) UnitType v_2')));
  CryptolToLean.SAWCorePreludeExtra.iteM (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) (Bind.bind x__
  (fun v_2 => Pure.pure (Pair_fst Bool (PairType (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) UnitType) v_2)))
  (Bind.bind x__' (fun v_1 => Bind.bind (Pure.pure (bvNat
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  CryptolToLean.SAWCorePrimitives.one_macro))) (fun v_2 => Pure.pure (bvAdd
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1 v_2)))) x__')) (subNat i'
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  CryptolToLean.SAWCorePrimitives.one_macro)) h_bounds_)))

/-- One element of the closed-form step: seed `0` below index 1, else
a conditional increment of the previous chain element, keyed on the
INPUT bit (not on the recursive vector). -/
noncomputable def pcElem (bits : Vec 32 Bool) (v : Vec 33 (Vec 32 Bool))
    (i : Nat) (hi : i < 33) : Vec 32 Bool :=
  if h : i < 1 then bvNat 32 0
  else
    (bif bits[i - 1]'(by omega) then
      bvAdd 32 (v[i - 1]'(by omega)) (bvNat 32 1)
    else v[i - 1]'(by omega))

/-- The closed-form step: what one pcBody application computes on a
pure input. -/
noncomputable def pcStep (bits : Vec 32 Bool) (v : Vec 33 (Vec 32 Bool)) :
    Vec 33 (Vec 32 Bool) :=
  Vector.ofFn (fun i : Fin 33 => pcElem bits v i.val i.isLt)

theorem pcBody_pure_eq (bits : Vec 32 Bool) (v : Vec 33 (Vec 32 Bool)) :
    pcBody (Pure.pure bits) (Pure.pure v) = Pure.pure (pcStep bits v) := by
  show pcBody (Except.ok bits) (Except.ok v) = Except.ok (pcStep bits v)
  unfold pcBody pcStep
  refine genWithBoundsM_eq_ok _ (pcElem bits v) ?_
  intro i hi
  by_cases h1 : i < 1
  · have hi0 : i = 0 := by omega
    subst hi0
    simp [CryptolToLean.SAWCorePreludeExtra.iteM, ltNat, pcElem,
          atRuntimeCheckedM, Pure.pure, Bind.bind, Except.bind,
          Except.pure]
  · have hcond : ltNat i (natPos_macro one_macro) = false := by
      simp [ltNat_eq_decide_lt, h1]
    rw [hcond, iteM_pure_false]
    refine Eq.trans (atWithProof_gen_ok (n := 32) _
      (fun j hj =>
        bif bits[j]'(by omega) then
          bvAdd 32 (v[j]'(by omega)) (bvNat 32 1)
        else v[j]'(by omega))
      (subNat i (natPos_macro one_macro)) _ ?_) ?_
    · intro j hj
      -- numerals FIRST: rw/simp matching cannot see through the
      -- macro chains, so normalize them to literals before anything
      -- keyed on concrete lengths
      simp only [natPos_macro, bit1_macro, bit0_macro, one_macro,
                 zero_macro, Nat.reduceMul, Nat.reduceAdd]
      -- reduce the wrapped zip selection WITHOUT whnf-ing the
      -- underlying `Vector.ofFn` (zip_getElem_lt), then close the
      -- value-level branch with iteM_ok_ok
      simp only [Pure.pure, Bind.bind, Except.bind, Except.pure,
                 atWithProof_checkedM]
      simp only [Vector_get_eq_getElem, Pair_fst, Pair_snd]
      rw [iteM_ok_ok]
      -- the zip selection needs an explicitly retyped instance: the
      -- lemma's collection length is `Nat.min 32 33`, the goal's is
      -- the (reducible) literal 32, and simp/rw matching does not
      -- unfold `Nat.min` — so state the equation at the goal's
      -- instance and let defeq coerce the library proof into it
      have hz : @GetElem.getElem
          (Vec 32 (PairType Bool (PairType (Vec 32 Bool) UnitType)))
          Nat _ _ _
          (zip Bool (Vec 32 Bool) 32 33 bits v) j hj
          = PairType.PairValue (bits[j]'hj)
              (PairType.PairValue (v[j]'(by omega)) UnitType.Unit) :=
        zip_getElem_lt 32 33 bits v j hj
      rw [hz]
    · simp [pcElem, h1]

/-- H_prod for the popcount body — every field by unfolding the
concrete body (amendment A: proven, never assumed). The branches of
one element use only `v[i-1]`, and the branch CONDITION comes from
`bits` (independent of `v`), so lookback has the same shape as
running_sum's. -/
theorem pc_h_prod (bits : Vec 32 Bool) :
    saw_fix_bounded_productive 33 (Vec 32 Bool) (pcBody (Pure.pure bits)) := by
  refine ⟨⟨Vector.replicate 33 (bvNat 32 0)⟩, ?_, ?_⟩
  · intro v
    exact ⟨pcStep bits v, pcBody_pure_eq bits v⟩
  · intro v₁ v₂ w₁ w₂ h₁ h₂ i hi hpre
    have e₁ : w₁ = pcStep bits v₁ := by
      have h := (pcBody_pure_eq bits v₁).symm.trans h₁
      exact ((Except.ok.injEq _ _).mp h).symm
    have e₂ : w₂ = pcStep bits v₂ := by
      have h := (pcBody_pure_eq bits v₂).symm.trans h₂
      exact ((Except.ok.injEq _ _).mp h).symm
    subst e₁ e₂
    unfold pcStep
    simp only [Vector.getElem_ofFn, pcElem]
    by_cases h1 : i < 1
    · simp [h1]
    · simp only [h1, dif_neg, not_false_iff]
      have hv : v₁[i - 1]'(by omega) = v₂[i - 1]'(by omega) :=
        hpre (i - 1) (by omega) (by omega)
      rw [hv]

/-- The closed-form solution chain: `pcChain k` counts the set bits
among `bits[0..k-1]`, as a conditional-increment chain from zero. -/
noncomputable def pcChain (bits : Vec 32 Bool) : Nat → Vec 32 Bool
  | 0 => bvNat 32 0
  | k + 1 =>
    if h : k < 32 then
      (bif bits[k]'h then bvAdd 32 (pcChain bits k) (bvNat 32 1)
       else pcChain bits k)
    else pcChain bits k

/-- The closed-form solution vector. -/
noncomputable def pcSol (bits : Vec 32 Bool) : Vec 33 (Vec 32 Bool) :=
  Vector.ofFn (fun i : Fin 33 => pcChain bits i.val)

/-- The closed form is a fixed point of the body. -/
theorem pc_sol_fixed (bits : Vec 32 Bool) :
    pcBody (Pure.pure bits) (Pure.pure (pcSol bits)) =
      Pure.pure (pcSol bits) := by
  rw [pcBody_pure_eq]
  show Except.ok (pcStep bits (pcSol bits)) = Except.ok (pcSol bits)
  -- at N = 33 the running_sum-style `congr 1` defeq close hits the
  -- whnf budget (quadratic chain re-evaluation), so go elementwise:
  -- index i of one step applied to the chain IS chain element i.
  apply congrArg
  apply Vector.ext
  intro i hi
  simp only [pcStep, Vector.getElem_ofFn, pcElem]
  by_cases h1 : i < 1
  · have hi0 : i = 0 := by omega
    subst hi0
    simp [pcSol, Vector.getElem_ofFn, pcChain]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < 32 := by omega
    simp only [dif_neg h1, Nat.add_sub_cancel, pcSol,
               Vector.getElem_ofFn, pcChain, dif_pos hk]

/-- The emitted realization collapses to the closed form. -/
theorem pc_choose_eq (bits : Vec 32 Bool)
    (H : saw_fix_bounded_productive 33 (Vec 32 Bool)
      (pcBody (Pure.pure bits))) :
    saw_fix_bounded_choose 33 (Vec 32 Bool) (pcBody (Pure.pure bits)) H =
      Pure.pure (pcSol bits) :=
  (saw_fix_bounded_choose_unique_pure_fixed_point 33 (Vec 32 Bool)
    (pcBody (Pure.pure bits)) H (pcSol bits) (pc_sol_fixed bits)).symm

/-- Bridge: the `Nat.rec` iteration produced by
`foldl_eq_natRec_atWithDefault` on the spec's fold step IS the
closed-form chain (index by index; `atWithDefault` stays in bounds
throughout). -/
theorem pc_natRec_eq (bits : Vec 32 Bool) :
    ∀ k, k ≤ 32 →
      Nat.rec (motive := fun _ => Vec 32 Bool) (bvNat 32 0)
        (fun i acc =>
          bif atWithDefault 32 Bool false bits i then
            bvAdd 32 acc (bvNat 32 1)
          else acc) k
      = pcChain bits k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm1
    have hm : m < 32 := by omega
    simp only [pcChain, dif_pos hm]
    rw [← ih (by omega)]
    rw [← atWithDefault_lt (n := 32) false bits m hm]

end PCDischarge

/-- Push `vecToBitVec` through the Bool-cond that `pcChain`'s steps
    leave behind. -/
theorem vTB_cond (c : Bool) (a b : Vec 32 Bool) :
    vecToBitVec (bif c then a else b)
      = bif c then vecToBitVec a else vecToBitVec b := by
  cases c <;> rfl

noncomputable def goal : Prop :=
  (x0 : Vec (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) -> let x := (Pure.pure
  x0); let x__ := (Pure.pure (bvNat (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))))))))))))))))))))))))))));
  let x__' := (Bind.bind (Bind.bind (Pure.pure (bvNat
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))))))))))))))))))))))))))))))
  (fun v_1'' => Bind.bind (Bind.bind (Pure.pure (bvNat
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))))))))))))))))))))))))))))))
  (fun v_1' => Bind.bind (Bind.bind x (fun v_1 => Pure.pure (bvShr
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))) (fun v_2 => Pure.pure (bvAnd
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1' v_2))))
  (fun v_2' => Pure.pure (bvMul (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1'' v_2'))))
  (fun v_1''' => Bind.bind x (fun v_2'' => Pure.pure (bvAdd
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1''' v_2''))));
  let x__'' := (Bind.bind (Bind.bind x__ (fun v_1 => Bind.bind x__'
  (fun v_2 => Pure.pure (bvAnd (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1 v_2))))
  (fun v_1'' => Bind.bind (Bind.bind x__ (fun v_1' => Bind.bind (Bind.bind x__'
  (fun v_1 => Pure.pure (bvShr (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))) (fun v_2 => Pure.pure (bvAnd
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1' v_2))))
  (fun v_2' => Pure.pure (bvAdd (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1'' v_2'))));
  let x__''' := (Bind.bind (Pure.pure (bvNat
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))))))))))))))))))))))))))
  (fun v_1'' => Bind.bind (Bind.bind x__'' (fun v_1' => Bind.bind (Bind.bind
  x__'' (fun v_1 => Pure.pure (bvShr
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) (fun v_2 => Pure.pure (bvAdd
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1' v_2))))
  (fun v_2' => Pure.pure (bvAnd (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1'' v_2'))));
  let x__'''' := (Bind.bind x__''' (fun v_1' => Bind.bind (Bind.bind x__'''
  (fun v_1 => Pure.pure (bvShr (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))) (fun v_2 => Pure.pure (bvAdd
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1' v_2)))); @Eq.{1} (Except
  String Bool) (Bind.bind (Bind.bind (Pure.pure (bvNat
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))))) (fun v_1'' => Bind.bind
  (Bind.bind x__'''' (fun v_1' => Bind.bind (Bind.bind x__''''
  (fun v_1 => Pure.pure (bvShr (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))))) (fun v_2 => Pure.pure (bvAdd
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1' v_2))))
  (fun v_2' => Pure.pure (bvAnd (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1'' v_2'))))
  (fun v_1''' => Bind.bind (let h_bounds_obligation_ : (Prop) := (LT.lt
  CryptolToLean.SAWCorePrimitives.zero_macro
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))));
  let h_bounds_ : (h_bounds_obligation_) := ((by (try unfold h_bounds_obligation_); (first | assumption | omega | (simp only [natPos_macro, bit0_macro, bit1_macro, one_macro, zero_macro, succ_macro, subNat, addNat, mulNat, minNat, maxNat, divNat_eq_div, modNat_eq_mod, divNat_checked_eq_div, modNat_checked_eq_mod, Nat.sub_eq, Nat.add_eq, Nat.mul_eq] at *; omega) | skip)));
  atWithProof_checkedM (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) (genWithBoundsM
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool)
  (fun (i : Nat) (h_gen_bounds_ : LT.lt i
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro))))))) => let h_bounds_obligation_ : (Prop) := (LT.lt
  (subNat (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) i)
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))));
  let h_bounds_ : (h_bounds_obligation_) := ((by (try unfold h_bounds_obligation_); (first | assumption | omega | (simp only [natPos_macro, bit0_macro, bit1_macro, one_macro, zero_macro, succ_macro, subNat, addNat, mulNat, minNat, maxNat, divNat_eq_div, modNat_eq_mod, divNat_checked_eq_div, modNat_checked_eq_mod, Nat.sub_eq, Nat.add_eq, Nat.mul_eq] at *; omega) | skip)));
  atWithProof_checkedM (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool)
  (let fix_body_ := (PCDischarge.pcBody x);
  let h_fix_prod_obligation_ : (Prop) := (saw_fix_bounded_productive
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) fix_body_);
  let h_fix_prod_ : (h_fix_prod_obligation_) := ((PCDischarge.pc_h_prod x0));
  saw_fix_bounded_choose (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit1_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) (Vec
  (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) Bool) fix_body_ h_fix_prod_)
  (subNat (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) i) h_bounds_))
  CryptolToLean.SAWCorePrimitives.zero_macro h_bounds_) (fun v_2'' => Pure.pure
  (bvEq (CryptolToLean.SAWCorePrimitives.natPos_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  (CryptolToLean.SAWCorePrimitives.bit0_macro
  CryptolToLean.SAWCorePrimitives.one_macro)))))) v_1''' v_2'')))) (Pure.pure
  Bool.true)


set_option maxRecDepth 100000 in
theorem goal_holds : goal := by
  intro x
  simp only [natPos_macro, bit1_macro, bit0_macro, one_macro,
             zero_macro, subNat, Nat.reduceMul, Nat.reduceAdd]
  set_option trace.Meta.Tactic.simp.unify true in
  set_option pp.deepTerms false in
  set_option pp.maxSteps 300 in
  simp only [PCDischarge.pc_choose_eq]
  simp only [Pure.pure, Bind.bind, Except.bind, Except.pure,
    atWithProof_checkedM, genWithBoundsM, PCDischarge.pcSol,
    ofFnM_except_ok, Vector.getElem_ofFn, Nat.reduceSub, bvEq_refl,
    Except.ok.injEq]
  unfold bvEq
  refine decide_eq_true ?_
  simp only [PCDischarge.pcChain, Nat.reduceLT, reduceDIte, Nat.reduceSub,
    Fin.isValue, Fin.val_zero,
    vecToBitVec_bvAnd, vecToBitVec_bvMul, vecToBitVec_bvNat,
    vecToBitVec_bvAdd, vecToBitVec_bvShr, vTB_cond]
  simp only [← getMsbD_vecToBitVec_lt,
    natPos_macro, bit0_macro, bit1_macro, one_macro, zero_macro,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT]
  bv_decide
