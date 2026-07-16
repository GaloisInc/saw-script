/-
Case Study: PER-GOAL SOLVER ROUTING — the Lean discharge.

The companion workflow verifies `f = h . g` (f(x) = 6*x) with a
SINGLE `llvm_verify` whose two proof obligations are routed to
DIFFERENT solvers per goal number via `goal_num_ite`:

  route.c (g doubles, h triples, f composes them)
       │
       │  llvm_verify m "f" ... (goal_num_ite 1 (offline_lean ...) w4)
       ▼
  workflows/llvm_goal_routing/test_llvm_goal_routing.saw
       │      goal 0 (h's precondition 2*x > 1)  → w4 (SMT) discharges
       │      goal 1 (f's postcondition)         → offline_lean EMITS
       ▼
  workflows/llvm_goal_routing/
      test_llvm_goal_routing.f_postcond_LLVM_points-to1.lean
       │
       │  this file imports Emitted and discharges goal 1
       ▼
  proofs/llvm_goal_routing/proof.lean    ←  YOU ARE HERE

The emitted goal is the full verification condition for f's
postcondition, wrapped in the `Except String Bool` monad with the
precondition hypotheses baked in as `iteM` guards:

  ∀ x : [64].
    precond(x) ⟹ ( precond(x) ∧ (2*x > 1) ⟹ 3*(2*x) == 6*x )

where precond(x) = (0 < x) ∧ (x < 2^63). Every guard branch that is
not vacuously `true` bottoms out in the SAME arithmetic core:

    bvMul 64 3 (bvMul 64 2 x) = bvMul 64 6 x

i.e. bitvector-mul associativity plus the constant fold 3*2 = 6. That
core is UNCONDITIONALLY valid (modular arithmetic), so the whole
guarded proposition collapses to `pure true`. `route_mul` proves the
core through the `Vec ↔ BitVec` round-trip and `BitVec.mul_assoc`;
`goal_closed` case-splits the three symbolic `bvult` guards and lets
`simp` reduce every `iteM`/monad layer, closing the arithmetic branch
with `route_mul` and `bvEq_refl`.

This proof depends only on `propext`, `Classical.choice`, `Quot.sound`
(from `simp`/`decide`) and the allowlisted converter round-trip axiom
`vecToBitVec_bitVecToVec` — no sorryAx, no bv_decide, no new axiom.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

-- Core arithmetic fact: 3 * (2 * x) = 6 * x over 64-bit bitvectors.
-- Peel the inner `bitVecToVec ∘ vecToBitVec` round-trip, reassociate
-- the BitVec product, and fold the concrete 3*2 = 6.
theorem route_mul (x : Vec 64 Bool) :
    bvMul 64 (bvNat 64 3) (bvMul 64 (bvNat 64 2) x) = bvMul 64 (bvNat 64 6) x := by
  unfold bvMul bvNat
  simp only [vecToBitVec_bitVecToVec]
  congr 1
  rw [← BitVec.mul_assoc]
  rw [show (3#64 * 2#64 : BitVec 64) = 6#64 from by decide]

theorem goal_closed : goal := by
  intro x
  by_cases h0 : bvult 64 (bvNat 64 0) x = true
  all_goals (by_cases h1 : bvult 64 x (bvNat 64 0x8000000000000000) = true)
  all_goals (by_cases h2 : bvult 64 (bvNat 64 1) (bvMul 64 (bvNat 64 2) x) = true)
  all_goals
    (simp_all [Bind.bind, Pure.pure, Except.bind, Except.pure,
      CryptolToLean.SAWCorePreludeExtra.iteM, route_mul, bvEq_refl])
