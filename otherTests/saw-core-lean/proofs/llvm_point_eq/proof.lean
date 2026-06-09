/-
Case Study A: LLVM Point verify with Lean discharge.

The first end-to-end test of the canonical SAW workflow with the
Lean backend as the prover for one obligation:

  exercises/functional-correctness/point/point.c (LLVM impl)
       │
       │  llvm_verify against Cryptol's `point_eq`
       ▼
  drivers/llvm_point_verify/test_llvm_point_verify.saw
       │
       │  (offline_lean) emits the equivalence obligation
       ▼
  drivers/llvm_point_verify/test_llvm_point_verify.point_eq_return_value_matching0.lean
       │
       │  this file imports Emitted and discharges
       ▼
  proofs/llvm_point_eq/proof.lean    ←  YOU ARE HERE

The emitted goal is:
  ∀ p1.x p1.y p2.x p2.y : [32].
    [bvEq 1 (C-side) #v[Cryptol-side]] = true

where:
  - C-side       = ite (bvEq 32 p2.x p1.x) (ite (bvEq 32 p2.y p1.y) [1] [0]) [0]
  - Cryptol-side = ite (bvEq 32 p1.x p2.x) (ite (bvEq 32 p1.y p2.y) true false) false

The two sides agree once we (a) note bvEq is commutative (bvEq_sym)
and (b) case-split on the per-coordinate equality outcomes. Each of
the four cases reduces to a closed bvEq on 1-bit literals.

This proof depends only on `propext` (used by simp_all) — no
sorryAx, no support-library axioms beyond what's already in the
trusted core. The whole thing fits in 6 lines of tactic.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

theorem goal_closed : goal := by
  intro x1 y1 x2 y2
  by_cases hx : bvEq 32 x1 x2 = true
  all_goals (by_cases hy : bvEq 32 y1 y2 = true)
  all_goals
    (simp_all [CryptolToLean.SAWCorePreludeExtra.ite, bvEq_sym]
     <;> rfl)
