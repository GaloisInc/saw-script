/-
ChaCha20 quarterround verify Lean discharge — the §4.1 headline demo.

The SAW driver `llvm_chacha20_q_verify` calls the unmodified
reference `qround` from `examples/chacha20/chacha20.c` on a
symbolic 16-word state, then asserts via `llvm_points_to` that
the post-call state equals the Cryptol-spec `qround` output
spliced into the input state at column-round positions
(0, 4, 8, 12). The Cryptol spec is the unmodified
`deps/cryptol-specs/.../chacha20.cry`.

The emitted Lean goal compares the LLVM-computed post-state and
the Cryptol-spec post-state element-wise via
  `foldr ∧ true (gen 16 Bool (\i -> bvEq 32 LLVM[i] Cryptol[i])) = true`.

For 12 indices (the unchanged state positions), the bvEq is
trivially true; for 4 indices (the qround output positions) it's
a 32-bit BitVec equation `bv_decide` discharges via SAT.

This is the headline pre-release demo: every step from C source
through Cryptol spec to Lean kernel-checked proof.
-/

import Emitted

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs
open CryptolToLean.SAWCorePreludeExtra

theorem goal_closed : goal := by
  intro state
  -- Apply the parametric `foldr_and_gen_eq_true_of_all` bridge: reduces
  -- the foldr-AND-of-gen to "∀ i < 16, the i-th bvEq is true".
  apply foldr_and_gen_eq_true_of_all 16
  intro i hi
  -- Case-split i ∈ [0, 16). 12 positions are trivial passthrough
  -- (state[i] = state[i], closed by `bvEq_refl` after `simp` peels the
  -- atWithDefault on literal #v[...]); 4 positions (i ∈ {0, 4, 8, 12})
  -- carry the qround equations, closed by:
  --   - `simp`: peels atWithDefault on literal #v[...] vec
  --   - `rw bvEq_true_iff_BitVec_eq`: converts bvEq to BitVec equality
  --   - `simp` with `vecToBitVec_bv*`: pushes vecToBitVec through BV ops
  --   - `bv_decide`: bitblasts via LRAT-checked SAT
  match i, hi with
  | 0, _ =>
    simp; rw [bvEq_true_iff_BitVec_eq]
    simp only [vecToBitVec_bvAdd, vecToBitVec_bvXor, vecToBitVec_bvOr,
               vecToBitVec_bvShl, vecToBitVec_bvShr, vecToBitVec_rotateL]
    bv_decide
  | 1, _ => simp; exact bvEq_refl _ _
  | 2, _ => simp; exact bvEq_refl _ _
  | 3, _ => simp; exact bvEq_refl _ _
  | 4, _ =>
    simp; rw [bvEq_true_iff_BitVec_eq]
    simp only [vecToBitVec_bvAdd, vecToBitVec_bvXor, vecToBitVec_bvOr,
               vecToBitVec_bvShl, vecToBitVec_bvShr, vecToBitVec_rotateL]
    bv_decide
  | 5, _ => simp; exact bvEq_refl _ _
  | 6, _ => simp; exact bvEq_refl _ _
  | 7, _ => simp; exact bvEq_refl _ _
  | 8, _ =>
    simp; rw [bvEq_true_iff_BitVec_eq]
    simp only [vecToBitVec_bvAdd, vecToBitVec_bvXor, vecToBitVec_bvOr,
               vecToBitVec_bvShl, vecToBitVec_bvShr, vecToBitVec_rotateL]
    bv_decide
  | 9, _ => simp; exact bvEq_refl _ _
  | 10, _ => simp; exact bvEq_refl _ _
  | 11, _ => simp; exact bvEq_refl _ _
  | 12, _ =>
    simp; rw [bvEq_true_iff_BitVec_eq]
    simp only [vecToBitVec_bvAdd, vecToBitVec_bvXor, vecToBitVec_bvOr,
               vecToBitVec_bvShl, vecToBitVec_bvShr, vecToBitVec_rotateL]
    bv_decide
  | 13, _ => simp; exact bvEq_refl _ _
  | 14, _ => simp; exact bvEq_refl _ _
  | 15, _ => simp; exact bvEq_refl _ _
  | _+16, h => exact absurd h (by omega)
