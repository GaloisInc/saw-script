/-
Discharge proof for test_llvm_double_extract_prove0.

Cryptol property: \x -> double_ref x == double_imp x, where the two
functions are `llvm_extract`ed from double.bc:
  double_ref(x) = x * 2   double_imp(x) = x << 1.

So the emitted obligation is the "multiply-by-two is shift-left-by-one"
bitvector identity, bvMul 32 2 x == bvShl 32 x 1. Proved by lifting the
BitVec fact `2 * b = b <<< 1` (via BitVec.twoPow_mul_eq_shiftLeft)
through the Vec ↔ BitVec coherence, then reflecting bvEq to `true`.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

theorem goal_closed : goal := by
  intro x
  simp only [natPos_macro, bit0_macro, one_macro, Nat.reduceMul]
  -- Core bitvector identity: multiplying by two IS shifting left by one.
  have hbv : ∀ b : BitVec 32, (BitVec.ofNat 32 2) * b = b <<< 1 := by
    intro b
    rw [show (BitVec.ofNat 32 2) = BitVec.twoPow 32 1 from by decide,
        BitVec.twoPow_mul_eq_shiftLeft]
  -- Lift it to the SAW `Vec` surface: double_ref x (= bvMul 2 x) equals
  -- double_imp x (= bvShl x 1), with the shift amount bvToNat-reduced to 1.
  have hkey : bvMul 32 (bvNat 32 2) x = bvShl 32 x (bvToNat 32 (bvNat 32 1)) := by
    rw [bvToNat_bvNat 32 1 (by decide)]
    unfold bvMul bvShl bvNat
    rw [vecToBitVec_bitVecToVec, hbv]
  -- Discharge the emitted Except-monad equality: both sides now agree, so
  -- bvEq reflects to `true`.
  simp only [Pure.pure, Bind.bind, Except.pure, Except.bind, hkey, bvEq_refl]
