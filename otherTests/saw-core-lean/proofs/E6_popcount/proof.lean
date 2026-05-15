/-
Width-4 popcount discharge via the §4.1 `genFixIdx_eq_recurrence_bounded`
bridge.

This replaces the previous `decide`-based stopgap with a real
bridge-based proof: peel SAW emission to expose `genFixIdx body 4`,
apply the bounded recurrence bridge to rewrite as `Nat.rec` form,
then close the residual `foldl ↔ Nat.rec` equality at concrete
width 4 via `decide`.

Why this matters for ChaCha20 (#174): the same shape applies, just
at width 32 / 80 / etc. The width-32 popcount discharge will be
*identical in structure* to this proof — only the final `decide`
step is replaced by `bv_decide` (SAT-based, scales).

Cryptol property:
  popCount_fold  bits = foldl (\acc b -> if b then acc + 1 else acc) 0 bits
  popCount_naive bits = ic ! 0
    where ic = [0] # [ if elt then prev + 1 else prev | elt <- bits | prev <- ic ]
  property eq bits = popCount_fold bits == popCount_naive bits
-/

import Emitted

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

namespace CaseE6

/-- Per-step accumulator: `if bits[k] then acc + 1 else acc`.
This is the closed-form recurrence step that the popcount-shape
body realizes. Using a named def here lets us treat the chain as
a single shared expression in the bridge's `Nat.rec` form, which
sidesteps the exponential blowup that inline expansion would
cause (popcount's ite duplicates the accumulator into both
branches; n levels deep would have 2^n leaves). -/
noncomputable def step (bits : CryptolToLean.SAWCoreVectors.Vec 4 Bool) (k : Nat)
    (acc : CryptolToLean.SAWCoreVectors.Vec 3 Bool) :
    CryptolToLean.SAWCoreVectors.Vec 3 Bool :=
  CryptolToLean.SAWCorePreludeExtra.ite _
    (atWithDefault 4 Bool false bits k)
    (bvAdd 3 acc (bvNat 3 1)) acc

@[reducible] noncomputable def errFix : CryptolToLean.SAWCoreVectors.Vec 3 Bool :=
  error_unrestricted (CryptolToLean.SAWCoreVectors.Vec 3 Bool) "fix lookup out of bounds"

end CaseE6

open CaseE6

theorem goal_closed : goal := by
  intro bits
  -- (1) bvEq elimination.
  refine eq_imp_bvEq_eq_true 3 _ _ ?_
  -- (2) Peel atWithDefault on outer gen 5 at index 0 → reads at
  -- subNat 4 0 = 4.
  rw [atWithDefault_gen_lt 5 _ _ 0 (by decide)]
  rw [show subNat 4 0 = 4 from rfl]
  rw [atWithDefault_genFix_lt 5 _ _ _ 4 (by decide)]
  -- (3) Apply the bounded recurrence bridge. Goal direction is
  -- `foldl-form = genFixIdx body 4`; bridge produces
  -- `genFixIdx body 4 = Nat.rec seed step 4`. Use Eq.symm-flavor
  -- to substitute RHS.
  refine Eq.trans ?_ (genFixIdx_eq_recurrence_bounded _ errFix _
                        (bvNat 3 0) (step bits) 4 ?h_seed ?h_step).symm
  case h_seed =>
    -- body (\_ => errFix) 0 = bvNat 3 0. Reduces by rfl since at
    -- index 0 the popcount-shape body returns its seed-vec.
    rfl
  case h_step =>
    -- For each k < 4, body lookup (k+1) = step bits k (lookup k).
    -- Case-split on k; each case rfl-closes (concrete index +
    -- popcount-shape body reduces).
    intro lookup k hk h_lk
    match k, hk with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
  -- (4) Goal is now `foldl-form bits = Nat.rec (bvNat 3 0) (step bits) 4`.
  -- Both sides are closed concrete expressions over `bits`. Destructure
  -- bits into 4 booleans; close via decide (16 cases).
  obtain ⟨arr, harr⟩ := bits
  match arr, harr with
  | ⟨[b0, b1, b2, b3]⟩, _ =>
    revert b0 b1 b2 b3
    decide
