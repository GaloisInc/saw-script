/-
Proof gap: LLVM Salsa20 quarterround verify.

This file is preserved as a stress proof attempt, not an accepted backend
proof regression. It still uses `bv_decide` for the final 32-bit bitvector
identity; under the current backend trust policy, `bv_decide`/`bv_check`
native-evaluation axioms are not accepted for completed proof discharge.

Pure-bv-arith case study (rotations + XOR + add over 32-bit
words, no comprehension recursion). Discharges ONE of four
emitted goals from
  workflows/llvm_salsa20_q_verify/test_llvm_salsa20_q_verify.saw —
  specifically points-to3 (Cryptol-side index 0).

The other three positions (points-to0/1/2) are the same shape
with different shift constants; once one closes, the others
follow by the same tactic once an axiom-clean BV proof route exists.

The proof:
  1. Convert `bvEq w a b = true` to `vecToBitVec a = vecToBitVec b`.
  2. Reduce `atWithDefault N _ #v[…] i` for concrete `i` via
     unfolding; the dependent-if collapses on closed indices.
  3. Reduce `bvToNat _ (bvNat _ k) = k` for the closed shifts.
  4. Push every Vec-side bv op through to BitVec via the
     `vecToBitVec_bv*` bridges (added 2026-05-05 to
     SAWCoreBitvectors_proofs.lean) and the `vecToBitVec_rotateL`
     bridge.
  5. Generalize each `vecToBitVec yi` as a fresh BitVec variable.
  6. The remaining gap is the pure `BitVec` equation.

The bridge steps before the final BV obligation are checked Lean theorems, not
translator-side rewrites. The last line remains a known proof gap because
`bv_decide` introduces a proof-local native axiom on this class of goal.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

theorem goal_closed : goal := by
  intro y0 y1 y2 y3
  rw [bvEq_true_iff_BitVec_eq]
  -- Reduce literal-vec lookups via the @[simp] vec-of-4 lemmas.
  -- Push every Vec-side bv op through to BitVec.
  simp only [atWithDefault_4_lit_0, atWithDefault_4_lit_1,
             atWithDefault_4_lit_2, atWithDefault_4_lit_3,
             vecToBitVec_bvXor, vecToBitVec_bvOr, vecToBitVec_bvShl,
             vecToBitVec_bvShr, vecToBitVec_bvAdd, vecToBitVec_rotateL,
             show bvToNat 4 (bvNat 4 7) = 7 from bvToNat_bvNat 4 7 (by decide),
             show bvToNat 4 (bvNat 4 9) = 9 from bvToNat_bvNat 4 9 (by decide),
             show bvToNat 4 (bvNat 4 13) = 13 from bvToNat_bvNat 4 13 (by decide),
             show bvToNat 8 (bvNat 8 18) = 18 from bvToNat_bvNat 8 18 (by decide)]
  generalize vecToBitVec y0 = a
  generalize vecToBitVec y1 = b
  generalize vecToBitVec y2 = c
  generalize vecToBitVec y3 = d
  bv_decide
