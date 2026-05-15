/-
Case Study C: LLVM Salsa20 quarterround verify with Lean discharge.

Pure-bv-arith case study (rotations + XOR + add over 32-bit
words, no comprehension recursion). Discharges ONE of four
emitted goals from
  drivers/llvm_salsa20_q_verify/test_llvm_salsa20_q_verify.saw —
  specifically points-to3 (Cryptol-side index 0).

The other three positions (points-to0/1/2) are the same shape
with different shift constants; once one closes, the others
follow by the same tactic. We discharge one to validate the
hypothesis "pure-bv-arith case studies discharge cleanly via
`bv_decide`" (long-term plan §3 Case C); replicating to the
other three is mechanical follow-up.

The proof:
  1. Convert `bvEq w a b = true` to `vecToBitVec a = vecToBitVec b`.
  2. Reduce `atWithDefault N _ #v[…] i` for concrete `i` via
     unfolding; the dependent-if collapses on closed indices.
  3. Reduce `bvToNat _ (bvNat _ k) = k` for the closed shifts.
  4. Push every Vec-side bv op through to BitVec via the
     `vecToBitVec_bv*` bridges (added 2026-05-05 to
     SAWCoreBitvectors_proofs.lean) and the `vecToBitVec_rotateL`
     bridge.
  5. Generalize each `vecToBitVec yi` as a fresh BitVec variable
     so `bv_decide` sees a pure BitVec equation.
  6. `bv_decide`.

This depends on the §4.1-aligned bridge library (no axioms beyond
the existing Phase 9 vecToBitVec/bitVecToVec round-trip) — every
step is a Lean theorem checked by the kernel, none are
translator-side rewrites.
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
