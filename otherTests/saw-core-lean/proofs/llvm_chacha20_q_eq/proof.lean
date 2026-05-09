/-
ChaCha20 quarterround LLVM verify with Lean discharge — first
step toward the ChaCha20 release demo (#174). Closes ONE of four
emitted goals from
  drivers/llvm_chacha20_q_verify/test_llvm_chacha20_q_verify.saw —
specifically points-to0. The other three positions (points-to1/2/3)
are the same shape with different shift constants and accumulator
positions; once one closes, the others follow by identical tactic.

Pure-bv-arith — XOR, +, and rotate-left on 32-bit words via the
`(x << n) | (x >> (-n & 31))` C idiom that the C wrapper uses.
RFC 7539 spec uses Cryptol's `<<<`. Both reduce to bvOr+bvShl+bvShr
on the BitVec side, and `bv_decide` (SAT-based) closes.

Mirrors `proofs/llvm_salsa20_q_eq/proof.lean` (Case Study C, #144) —
the bridge-library lemmas (`bvEq_true_iff_BitVec_eq`,
`vecToBitVec_bv*`, `vecToBitVec_rotateL`) carry over unchanged.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

theorem goal_closed : goal := by
  intro a b c d
  rw [bvEq_true_iff_BitVec_eq]
  -- Push every Vec-side bv op through to BitVec.
  simp only [atWithDefault_4_lit_0, atWithDefault_4_lit_1,
             atWithDefault_4_lit_2, atWithDefault_4_lit_3,
             vecToBitVec_bvXor, vecToBitVec_bvOr, vecToBitVec_bvShl,
             vecToBitVec_bvShr, vecToBitVec_bvAdd, vecToBitVec_rotateL]
  -- Generalize the 4 input BitVecs so bv_decide sees a pure BV
  -- equation.
  generalize vecToBitVec a = ba
  generalize vecToBitVec b = bb
  generalize vecToBitVec c = bc
  generalize vecToBitVec d = bd
  bv_decide
