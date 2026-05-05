/-
Case Study D: fib-like comprehension at small width — Lean discharge.

Closes the running-sum equivalence by manual induction. The
strategy:

  1. Define `runSumPartial xs k`: the explicit running sum up to
     index k.
  2. Prove by induction that `genFixIdx … (the body) k =
     runSumPartial xs k` for `k ≤ 8`.
  3. Apply at k = 8 to reduce LHS to `runSumPartial xs 8`.
  4. Show `runSumPartial xs 8 = the explicit-sum RHS` (after
     `bvAdd_id_l` collapses the seed).
  5. Conclude via `bvEq_refl`.

Long proof; no `simp` wizardry, just step-by-step manual unfolds.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

namespace CaseD

-- Marked `@[reducible]` so `rw`/`simp` can match through the alias.
@[reducible] noncomputable def errVec : Vec 32 Bool :=
  error_unrestricted (Vec 32 Bool) "at: index out of bounds"

@[reducible] noncomputable def errFix : Vec 32 Bool :=
  error_unrestricted (Vec 32 Bool) "fix lookup out of bounds"

@[reducible] noncomputable def errPair :
    PairType (Vec 32 Bool) (PairType (Vec 32 Bool) UnitType) :=
  error_unrestricted (PairType (Vec 32 Bool) (PairType (Vec 32 Bool) UnitType))
    "at: index out of bounds"

-- Type abbreviations for the pair-of-pair shape from Cryptol's zip.
abbrev SAWPair := PairType (Vec 32 Bool) (PairType (Vec 32 Bool) UnitType)

/-- The body emitted for the running-sum comprehension. -/
noncomputable def body (xs : Vec 8 (Vec 32 Bool))
    (lookup0 : Nat → Vec 32 Bool) (idx0 : Nat) : Vec 32 Bool :=
  let inner_step (sums : Vec 9 (Vec 32 Bool)) (i2 : Nat) : Vec 32 Bool :=
    let p := atWithDefault 8 SAWPair errPair
              (zip (Vec 32 Bool) (Vec 32 Bool) 9 8 sums xs) i2
    bvAdd 32
      (Pair_fst (Vec 32 Bool) (PairType (Vec 32 Bool) UnitType) p)
      (Pair_fst (Vec 32 Bool) UnitType
        (Pair_snd (Vec 32 Bool) (PairType (Vec 32 Bool) UnitType) p))
  let inner_branch (sums : Vec 9 (Vec 32 Bool)) (i' : Nat) : Vec 32 Bool :=
    CryptolToLean.SAWCorePreludeExtra.ite (Vec 32 Bool) (ltNat i' 1)
      (atWithDefault 1 (Vec 32 Bool) errVec #v[bvNat 32 0] i')
      (atWithDefault 8 (Vec 32 Bool) errVec
        (gen 8 (Vec 32 Bool) (inner_step sums)) (subNat i' 1))
  let sums : Vec 9 (Vec 32 Bool) := gen 9 (Vec 32 Bool) lookup0
  atWithDefault 9 (Vec 32 Bool) errFix
    (gen 9 (Vec 32 Bool) (inner_branch sums)) idx0

/-- Explicit running-sum over the first k elements of xs. -/
noncomputable def runSumPartial (xs : Vec 8 (Vec 32 Bool)) : Nat → Vec 32 Bool
  | 0     => bvNat 32 0
  | k + 1 => bvAdd 32 (runSumPartial xs k) (atWithDefault 8 (Vec 32 Bool) errVec xs k)

/-- The body at index 0, with any lookup, returns the seed
(`bvNat 32 0`). h_seed for the bridge. -/
theorem body_seed (xs : Vec 8 (Vec 32 Bool)) (lookup0 : Nat → Vec 32 Bool) :
    body xs lookup0 0 = bvNat 32 0 := by
  unfold body atWithDefault gen ltNat CryptolToLean.SAWCorePreludeExtra.ite
  simp only [Vector.getElem_ofFn]
  -- Now goal involves dite (0 < 9) and Bool.rec on (decide (0 < 1)).
  -- Both conditions evaluate to the in-bounds branch via `rfl`.
  rfl

/-- The body at each concrete index k+1, for k ∈ {0, …, 7}.
We discharge each case separately; the symbolic-k version below
case-splits across these. -/
theorem body_step_at (xs : Vec 8 (Vec 32 Bool)) (lookup0 : Nat → Vec 32 Bool) :
    (body xs lookup0 1 = bvAdd 32 (lookup0 0)
        (atWithDefault 8 (Vec 32 Bool) errVec xs 0)) ∧
    (body xs lookup0 2 = bvAdd 32 (lookup0 1)
        (atWithDefault 8 (Vec 32 Bool) errVec xs 1)) ∧
    (body xs lookup0 3 = bvAdd 32 (lookup0 2)
        (atWithDefault 8 (Vec 32 Bool) errVec xs 2)) ∧
    (body xs lookup0 4 = bvAdd 32 (lookup0 3)
        (atWithDefault 8 (Vec 32 Bool) errVec xs 3)) ∧
    (body xs lookup0 5 = bvAdd 32 (lookup0 4)
        (atWithDefault 8 (Vec 32 Bool) errVec xs 4)) ∧
    (body xs lookup0 6 = bvAdd 32 (lookup0 5)
        (atWithDefault 8 (Vec 32 Bool) errVec xs 5)) ∧
    (body xs lookup0 7 = bvAdd 32 (lookup0 6)
        (atWithDefault 8 (Vec 32 Bool) errVec xs 6)) ∧
    (body xs lookup0 8 = bvAdd 32 (lookup0 7)
        (atWithDefault 8 (Vec 32 Bool) errVec xs 7)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (unfold body; rfl)

/-- Generic version of `genFixIdx_at_8`: takes an arbitrary body B
satisfying the running-sum recurrence shape (h_seed + 8 per-index
step equations), and concludes the explicit chain. The `body` def
above is one realization, but `goal_closed` will instantiate this
against the verbatim inline lambda from the emitted goal — sidestepping
the need to identify our `body xs` with that lambda via `show`/whnf. -/
theorem genFixIdx_at_8_generic
    (xs : Vec 8 (Vec 32 Bool))
    (B : (Nat → Vec 32 Bool) → Nat → Vec 32 Bool)
    (h_seed : ∀ lk, B lk 0 = bvNat 32 0)
    (h_steps :
        (∀ lk, B lk 1 = bvAdd 32 (lk 0) (atWithDefault 8 (Vec 32 Bool) errVec xs 0)) ∧
        (∀ lk, B lk 2 = bvAdd 32 (lk 1) (atWithDefault 8 (Vec 32 Bool) errVec xs 1)) ∧
        (∀ lk, B lk 3 = bvAdd 32 (lk 2) (atWithDefault 8 (Vec 32 Bool) errVec xs 2)) ∧
        (∀ lk, B lk 4 = bvAdd 32 (lk 3) (atWithDefault 8 (Vec 32 Bool) errVec xs 3)) ∧
        (∀ lk, B lk 5 = bvAdd 32 (lk 4) (atWithDefault 8 (Vec 32 Bool) errVec xs 4)) ∧
        (∀ lk, B lk 6 = bvAdd 32 (lk 5) (atWithDefault 8 (Vec 32 Bool) errVec xs 5)) ∧
        (∀ lk, B lk 7 = bvAdd 32 (lk 6) (atWithDefault 8 (Vec 32 Bool) errVec xs 6)) ∧
        (∀ lk, B lk 8 = bvAdd 32 (lk 7) (atWithDefault 8 (Vec 32 Bool) errVec xs 7))) :
    genFixIdx (Vec 32 Bool) errFix B 8 =
      bvAdd 32
        (bvAdd 32
          (bvAdd 32
            (bvAdd 32
              (bvAdd 32
                (bvAdd 32
                  (bvAdd 32
                    (bvAdd 32 (bvNat 32 0)
                      (atWithDefault 8 (Vec 32 Bool) errVec xs 0))
                    (atWithDefault 8 (Vec 32 Bool) errVec xs 1))
                  (atWithDefault 8 (Vec 32 Bool) errVec xs 2))
                (atWithDefault 8 (Vec 32 Bool) errVec xs 3))
              (atWithDefault 8 (Vec 32 Bool) errVec xs 4))
            (atWithDefault 8 (Vec 32 Bool) errVec xs 5))
          (atWithDefault 8 (Vec 32 Bool) errVec xs 6))
        (atWithDefault 8 (Vec 32 Bool) errVec xs 7) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_steps
  -- listBuild_getD_eq_genFixIdx is generic in the body, so it works for
  -- our opaque B without any instantiation.
  have lb : ∀ n j, j < n →
      (genFixListBuild (Vec 32 Bool) errFix B n).getD j errFix
        = genFixIdx (Vec 32 Bool) errFix B j := by
    intro n j hjn
    exact genFixListBuild_getD_eq_genFixIdx _ errFix B n j hjn
  conv => lhs; rw [show (8 : Nat) = 7 + 1 from rfl, genFixIdx_succ]
  rw [h8, lb 8 7 (by decide)]
  conv => lhs; rw [show (7 : Nat) = 6 + 1 from rfl, genFixIdx_succ]
  rw [h7, lb 7 6 (by decide)]
  conv => lhs; rw [show (6 : Nat) = 5 + 1 from rfl, genFixIdx_succ]
  rw [h6, lb 6 5 (by decide)]
  conv => lhs; rw [show (5 : Nat) = 4 + 1 from rfl, genFixIdx_succ]
  rw [h5, lb 5 4 (by decide)]
  conv => lhs; rw [show (4 : Nat) = 3 + 1 from rfl, genFixIdx_succ]
  rw [h4, lb 4 3 (by decide)]
  conv => lhs; rw [show (3 : Nat) = 2 + 1 from rfl, genFixIdx_succ]
  rw [h3, lb 3 2 (by decide)]
  conv => lhs; rw [show (2 : Nat) = 1 + 1 from rfl, genFixIdx_succ]
  rw [h2, lb 2 1 (by decide)]
  conv => lhs; rw [show (1 : Nat) = 0 + 1 from rfl, genFixIdx_succ]
  rw [h1, lb 1 0 (by decide)]
  rw [genFixIdx_zero, h_seed]

end CaseD

open CaseD

theorem goal_closed : goal := by
  intro xs
  refine eq_imp_bvEq_eq_true 32 _ _ ?_
  rw [atWithDefault_gen_lt 9 _ _ 0 (by decide)]
  rw [show subNat 8 0 = 8 from rfl]
  rw [atWithDefault_genFix_lt 9 _ _ _ 8 (by decide)]
  -- Apply the generic lemma via `refine`, splitting into subgoals
  -- so the per-index `rfl` checks happen in small contexts.
  refine Eq.trans (genFixIdx_at_8_generic xs _ ?h_seed ?h_steps) ?_
  case h_seed => intro lk; rfl
  case h_steps =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro lk; rfl)
  rw [bvAdd_id_l]
