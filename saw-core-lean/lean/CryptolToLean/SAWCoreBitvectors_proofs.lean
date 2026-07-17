/-
`CryptolToLean.SAWCoreBitvectors_proofs` — bv arithmetic/bitwise
lemmas, mostly proven from `Lean.BitVec` after Phase 9.

Mirrors the lemma set in
`saw-core-rocq/rocq/handwritten/CryptolToRocq/SAWCoreBitvectors.v`.

# Phase 9 trust posture

The bv ops in `SAWCorePrimitives.lean` are now `noncomputable
def`s routing through `Lean.BitVec` via `vecToBitVec` /
`bitVecToVec`. The two converter round-trip axioms
(`vecToBitVec_bitVecToVec`, `bitVecToVec_vecToBitVec`) are the
only soundness commitments — every other bv arithmetic /
bitwise / comparison property in this file is a *theorem*
proven from Lean's `BitVec` library plus those two coherence
axioms.

This file contains ZERO axiom declarations (audit 2026-07-14):
every lemma — including the signed/unsigned inequality predicates
(`isBvslt_to_isBvsle`, `isBvslt_antirefl`, `isBvule_zero_n`) and
the `bvNat`/`bvToNat` round-trip/bound facts (`bvNat_bvToNat_id`,
`bvToNat_bounds`) that were once deferred as axioms — is a proven
theorem. Rocq-counterpart citations on individual lemmas remain as
audit trail.
-/

import CryptolToLean.SAWCorePrimitives
import CryptolToLean.SAWCoreVectors
import CryptolToLean.SAWCorePreludeExtra
import CryptolToLean.SAWCorePrelude_proofs
import Std.Tactic.BVDecide

namespace CryptolToLean.SAWCoreBitvectorsProofs

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

-- AUDIT (2026-05-02): Lean-stdlib Bool theorems
-- (not_not / and_comm / and_assoc / or_comm / or_assoc /
-- and_or_distrib) were previously provided here. They were
-- removed in the slop sweep — these are properties of Lean's
-- stdlib `&&` / `||` / `!` operators, but SAW's Prelude bool ops
-- emit as `ite Bool a b Bool.false` chains in our translated
-- output (per leanOpaqueBuiltins + L-16 wrapper routing), so
-- standalone Lean Bool ops never surface in user-facing
-- SAW-translated goals. The walkthrough proof uses
-- `cases <;> rfl` directly through `iteDep`'s reducibility
-- (SAWCorePreludeExtra.iteDep is `@[reducible]`), without
-- needing these Lean-stdlib aliases. If a user-facing demo ever
-- surfaces actual `&&` / `||` outside SAW's lowering, those
-- theorems are in Lean's stdlib (`Bool.and_comm`, `Bool.or_assoc`,
-- etc.) — call them directly.

/-! ## Bitvector arithmetic theorems

Phase 9: each lemma below was an axiom transposing a Rocq
theorem; now provable from `Lean.BitVec` plus the converter
round-trip axioms. The unfold-and-`BitVec.lemma` pattern is
mechanical: peel off `bitVecToVec ∘ vecToBitVec`-pairs via
the round-trip, then close with the matching `BitVec` lemma. -/

/-- `bvAdd` left-identity. Rocq: `bvAdd_id_l`. -/
theorem bvAdd_id_l (w : Nat) (a : Vec w Bool) : bvAdd w (bvNat w 0) a = a := by
  unfold bvAdd bvNat
  rw [vecToBitVec_bitVecToVec, BitVec.zero_add, bitVecToVec_vecToBitVec]

/-- `bvAdd` right-identity. Rocq: `bvAdd_id_r`. -/
theorem bvAdd_id_r (w : Nat) (a : Vec w Bool) : bvAdd w a (bvNat w 0) = a := by
  unfold bvAdd bvNat
  rw [vecToBitVec_bitVecToVec, BitVec.add_zero, bitVecToVec_vecToBitVec]

/-- `bvAdd` commutativity. Rocq: `bvAdd_comm`. -/
theorem bvAdd_comm (w : Nat) (a b : Vec w Bool) : bvAdd w a b = bvAdd w b a := by
  unfold bvAdd
  rw [BitVec.add_comm]

/-- `bvAdd` associativity. Rocq: `bvAdd_assoc`. -/
theorem bvAdd_assoc (w : Nat) (a b c : Vec w Bool) :
    bvAdd w (bvAdd w a b) c = bvAdd w a (bvAdd w b c) := by
  unfold bvAdd
  rw [vecToBitVec_bitVecToVec, vecToBitVec_bitVecToVec, BitVec.add_assoc]

/-- `bvSub` right-zero. Rocq: `bvSub_n_zero`. -/
theorem bvSub_n_zero (w : Nat) (a : Vec w Bool) :
    bvSub w a (bvNat w 0) = a := by
  unfold bvSub bvNat
  rw [vecToBitVec_bitVecToVec, BitVec.sub_zero, bitVecToVec_vecToBitVec]

/-- `bvSub` left-zero is negation. Rocq: `bvSub_zero_n`. -/
theorem bvSub_zero_n (w : Nat) (a : Vec w Bool) :
    bvSub w (bvNat w 0) a = bvNeg w a := by
  unfold bvSub bvNeg bvNat
  rw [vecToBitVec_bitVecToVec, BitVec.zero_sub]

/-- `bvNeg` distributes over `bvAdd`. Rocq: `bvNeg_bvAdd_distrib`. -/
theorem bvNeg_bvAdd_distrib (w : Nat) (a b : Vec w Bool) :
    bvNeg w (bvAdd w a b) = bvAdd w (bvNeg w a) (bvNeg w b) := by
  unfold bvNeg bvAdd
  rw [vecToBitVec_bitVecToVec, vecToBitVec_bitVecToVec, vecToBitVec_bitVecToVec,
      BitVec.neg_add, BitVec.sub_eq_add_neg]

/-- `bvSub` rewrites to `bvAdd` of negation. Rocq:
`bvSub_eq_bvAdd_neg`. -/
theorem bvSub_eq_bvAdd_neg (w : Nat) (a b : Vec w Bool) :
    bvSub w a b = bvAdd w a (bvNeg w b) := by
  unfold bvSub bvAdd bvNeg
  rw [vecToBitVec_bitVecToVec, BitVec.sub_eq_add_neg]

/-! ## Bitvector xor theorems -/

/-- `bvXor` of a value with itself is zero. Rocq: `bvXor_same`. -/
theorem bvXor_same (n : Nat) (x : Vec n Bool) :
    bvXor n x x = bvNat n 0 := by
  unfold bvXor bvNat
  rw [BitVec.xor_self]

/-- `bvXor` zero-identity. Rocq: `bvXor_zero`. -/
theorem bvXor_zero (n : Nat) (x : Vec n Bool) :
    bvXor n x (bvNat n 0) = x := by
  unfold bvXor bvNat
  rw [vecToBitVec_bitVecToVec, BitVec.xor_zero, bitVecToVec_vecToBitVec]

/-- `bvXor` associativity. Rocq: `bvXor_assoc`. -/
theorem bvXor_assoc (n : Nat) (x y z : Vec n Bool) :
    bvXor n (bvXor n x y) z = bvXor n x (bvXor n y z) := by
  unfold bvXor
  rw [vecToBitVec_bitVecToVec, vecToBitVec_bitVecToVec, BitVec.xor_assoc]

/-- `bvXor` commutativity. Rocq: `bvXor_comm`. -/
theorem bvXor_comm (n : Nat) (x y : Vec n Bool) :
    bvXor n x y = bvXor n y x := by
  unfold bvXor
  rw [BitVec.xor_comm]

/-! ## Bitvector equality theorems

These connect `bvEq` (a SAW `Bool`) with Lean propositional
equality. Phase 9 makes these provable from the converter
round-trip plus `BitVec.eq_of_toNat_eq` / decidable equality. -/

/-- `bvEq` reflexivity. Rocq: `bvEq_refl`. -/
theorem bvEq_refl (w : Nat) (a : Vec w Bool) :
    bvEq w a a = Bool.true := by
  unfold bvEq
  simp

/-- `bvEq` symmetry. Rocq: `bvEq_sym`. -/
theorem bvEq_sym (w : Nat) (a b : Vec w Bool) :
    bvEq w a b = bvEq w b a := by
  unfold bvEq
  exact Bool.beq_comm

/-- `bvEq` is decision: returns `true` iff propositionally equal.
Rocq: `bvEq_eq`. -/
theorem bvEq_iff (w : Nat) (a b : Vec w Bool) :
    bvEq w a b = Bool.true ↔ a = b := by
  unfold bvEq
  rw [beq_iff_eq]
  constructor
  · intro h
    have : bitVecToVec (vecToBitVec a) = bitVecToVec (vecToBitVec b) := by rw [h]
    rwa [bitVecToVec_vecToBitVec, bitVecToVec_vecToBitVec] at this
  · intro h; rw [h]

/-- One direction of `bvEq_iff`, in convenient `=>` form. -/
theorem bvEq_eq_true_imp_eq
    (w : Nat) (a b : Vec w Bool) :
    bvEq w a b = Bool.true → a = b :=
  fun h => (bvEq_iff w a b).mp h

/-! ## Reduction shortcuts for `bvEq` scrutinee

The translator emits `iteDep (...) (bvEq w x y) trueBranch
falseBranch` for Cryptol's `==>` and `if x == y then ... else ...`.
Under a hypothesis on the value of `bvEq w x y`, users can chain
`simp [h]` (rewriting the scrutinee) with `simp` (using
`iteDep_True` / `iteDep_False` already in scope as `@[simp]`) to
reduce. No additional lemma needed. -/

/-! ## Rocq-parity bv constants and predicate wrappers (Phase 6)

Mirrors `saw-core-rocq/rocq/handwritten/CryptolToRocq/SAWCoreBitvectors.v`
lines 110-200ish. Constants: signed/unsigned min/max bv values.
Predicates: lift `bv*` Bool comparators to Prop. Each definition
here is constructive (computes via `gen` / `bvslt`/etc.); each
"axiom" is a faithful transposition of a Rocq theorem proven via
`holds_for_bits_up_to_3`. -/

/-- Signed-max bv value: `0111...1` (top bit clear, rest set).
Rocq: `bvsmax`. Phase 9: routes through Lean's `BitVec.intMax`
to align with our MSB-first `vecToBitVec` convention. -/
noncomputable def bvsmax (w : Nat) : Vec w Bool :=
  bitVecToVec (BitVec.intMax w)

/-- Signed-min bv value: `1000...0` (top bit set, rest clear).
Rocq: `bvsmin`. Phase 9: routes through `BitVec.intMin`. -/
noncomputable def bvsmin (w : Nat) : Vec w Bool :=
  bitVecToVec (BitVec.intMin w)

/-- Unsigned-max bv value: `111...1`. Rocq: `bvumax`. -/
def bvumax (w : Nat) : Vec w Bool := gen w Bool (fun _ => true)

/-- Unsigned-min bv value: `000...0`. Rocq: `bvumin`. -/
def bvumin (w : Nat) : Vec w Bool := gen w Bool (fun _ => false)

/-! ### Prop-wrappers around the Bool-valued comparators

Useful when chaining bv comparison with other Prop-valued
hypotheses. Each definition matches Rocq's
`isBvsle / isBvslt / isBvule / isBvult` exactly. -/

def isBvsle (w : Nat) (a b : Vec w Bool) : Prop := bvsle w a b = true
def isBvslt (w : Nat) (a b : Vec w Bool) : Prop := bvslt w a b = true
def isBvule (w : Nat) (a b : Vec w Bool) : Prop := bvule w a b = true
def isBvult (w : Nat) (a b : Vec w Bool) : Prop := bvult w a b = true

/-! ### Cross-comparison theorems

Phase 9: was axiomatic transposition of Rocq theorems proven by
`holds_for_bits_up_to_3`; now provable from `Lean.BitVec`
inequalities plus the Vec ↔ BitVec coherence. -/

/-- Strict-less implies less-or-equal (unsigned). Rocq: `isBvult_to_isBvule`. -/
theorem isBvult_to_isBvule (w : Nat) (a b : Vec w Bool) :
    isBvult w a b → isBvule w a b := by
  unfold isBvult isBvule bvult bvule
  intro h
  rw [BitVec.ult] at h
  rw [BitVec.ule]
  exact decide_eq_true ((decide_eq_true_iff).mp h |> Nat.le_of_lt)

/-- Less-or-equal splits as strict-less or equal. Rocq:
`isBvule_to_isBvult_or_eq`. -/
theorem isBvule_to_isBvult_or_eq (w : Nat) (a b : Vec w Bool) :
    isBvule w a b → isBvult w a b ∨ a = b := by
  unfold isBvule isBvult bvule bvult
  intro h
  rw [BitVec.ule] at h
  by_cases hab : vecToBitVec a = vecToBitVec b
  · right
    have : bitVecToVec (vecToBitVec a) = bitVecToVec (vecToBitVec b) := congrArg _ hab
    rwa [bitVecToVec_vecToBitVec, bitVecToVec_vecToBitVec] at this
  · left
    rw [BitVec.ult]
    refine decide_eq_true (Nat.lt_of_le_of_ne ((decide_eq_true_iff).mp h) ?_)
    intro hh
    apply hab
    apply BitVec.eq_of_toNat_eq
    exact hh

/-- Strict-less implies less-or-equal (signed). Rocq: `isBvslt_to_isBvsle`. -/
theorem isBvslt_to_isBvsle (w : Nat) (a b : Vec w Bool) :
    isBvslt w a b → isBvsle w a b := by
  unfold isBvslt isBvsle bvslt bvsle
  intro h
  rw [BitVec.slt] at h
  rw [BitVec.sle]
  exact decide_eq_true ((decide_eq_true_iff).mp h |> Int.le_of_lt)

/-- Strict-less implies bvEq is false (signed). Rocq:
`isBvslt_to_bvEq_false`. -/
theorem isBvslt_to_bvEq_false (w : Nat) (a b : Vec w Bool) :
    isBvslt w a b → bvEq w a b = false := by
  unfold isBvslt bvslt bvEq
  intro h
  rw [BitVec.slt] at h
  simp
  intro hab
  rw [hab] at h
  simp at h

/-- Strict-less implies bvEq is false (unsigned). Rocq:
`isBvult_to_bvEq_false`. -/
theorem isBvult_to_bvEq_false (w : Nat) (a b : Vec w Bool) :
    isBvult w a b → bvEq w a b = false := by
  unfold isBvult bvult bvEq
  intro h
  rw [BitVec.ult] at h
  simp
  intro hab
  rw [hab] at h
  simp at h

/-! ### Edge-case theorems

Boundary properties around `bvsmin` / `bvsmax` / `intToBv 0`.
Phase 9: unsigned cases (`isBvule_zero_n`, `isBvult_n_zero`) are
provable; signed cases stay axiomatic. -/

/-- Zero is unsigned-min. Rocq: `isBvule_zero_n`. -/
theorem isBvule_zero_n (w : Nat) (a : Vec w Bool) :
    isBvule w (intToBv w 0) a := by
  unfold isBvule bvule intToBv
  rw [vecToBitVec_bitVecToVec, BitVec.ule]
  simp

/-- Nothing is unsigned-strict-less than zero. Rocq: `isBvult_n_zero`. -/
theorem isBvult_n_zero (w : Nat) (a : Vec w Bool) :
    ¬ isBvult w a (intToBv w 0) := by
  unfold isBvult bvult intToBv
  rw [vecToBitVec_bitVecToVec, BitVec.ult]
  simp

/-- Antireflexivity of strict-less (signed). Rocq: `isBvslt_antirefl`. -/
theorem isBvslt_antirefl (w : Nat) (a : Vec w Bool) :
    ¬ isBvslt w a a := by
  unfold isBvslt bvslt
  rw [BitVec.slt]
  simp

/-- Antisymmetry of less-or-equal (signed). Rocq: `isBvsle_antisymm`. -/
theorem isBvsle_antisymm (w : Nat) (a b : Vec w Bool) :
    isBvsle w a b → isBvsle w b a → a = b := by
  unfold isBvsle bvsle
  intros h1 h2
  rw [BitVec.sle] at h1 h2
  have heq : vecToBitVec a = vecToBitVec b := by
    apply BitVec.eq_of_toInt_eq
    have l1 : (vecToBitVec a).toInt ≤ (vecToBitVec b).toInt := (decide_eq_true_iff).mp h1
    have l2 : (vecToBitVec b).toInt ≤ (vecToBitVec a).toInt := (decide_eq_true_iff).mp h2
    omega
  have : bitVecToVec (vecToBitVec a) = bitVecToVec (vecToBitVec b) := congrArg _ heq
  rwa [bitVecToVec_vecToBitVec, bitVecToVec_vecToBitVec] at this

/-- The only thing unsigned-≤ zero is zero. Rocq: `isBvule_n_zero`. -/
theorem isBvule_n_zero (w : Nat) (a : Vec w Bool) :
    isBvule w a (intToBv w 0) ↔ a = intToBv w 0 := by
  unfold isBvule bvule intToBv
  rw [vecToBitVec_bitVecToVec, BitVec.ule]
  simp
  constructor
  · intro h
    have heq : vecToBitVec a = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp
      exact h
    have : bitVecToVec (vecToBitVec a) = bitVecToVec 0 := congrArg _ heq
    rwa [bitVecToVec_vecToBitVec] at this
  · intro h
    rw [h]
    rw [vecToBitVec_bitVecToVec]
    simp

/-! ### Edge-case theorems

Phase 9: signed boundary properties around `bvsmin`/`bvsmax`,
now provable since both are defined via Lean's
`BitVec.intMin`/`intMax`. -/

/-- Nothing is signed-less than `bvsmin`. Rocq: `not_isBvslt_bvsmin`. -/
theorem not_isBvslt_bvsmin (w : Nat) (a : Vec w Bool) :
    ¬ isBvslt w a (bvsmin w) := by
  unfold isBvslt bvslt bvsmin
  rw [vecToBitVec_bitVecToVec]
  simp [BitVec.slt]
  exact BitVec.toInt_intMin_le (vecToBitVec a)

/-- `bvsmax` is signed-greatest. Rocq: `not_isBvslt_bvsmax`. -/
theorem not_isBvslt_bvsmax (w : Nat) (a : Vec w Bool) :
    ¬ isBvslt w (bvsmax w) a := by
  unfold isBvslt bvslt bvsmax
  rw [vecToBitVec_bitVecToVec]
  simp [BitVec.slt, BitVec.toInt_intMax]
  exact BitVec.toInt_le

/-! ### bv round-trip theorems

Phase 9: `bvNat`/`bvToNat` round-trip; was axiomatic, now
provable from `Lean.BitVec` plus the Vec ↔ BitVec coherence
axioms. -/

/-- Round-tripping a bv through `bvToNat` and back gives the
original. Rocq: `bvNat_bvToNat_id`. -/
theorem bvNat_bvToNat_id (w : Nat) (a : Vec w Bool) :
    bvNat w (bvToNat w a) = a := by
  unfold bvNat bvToNat
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, bitVecToVec_vecToBitVec]

/-- Converse round-trip: `bvNat → bvToNat → original Nat`,
provided the input is in-bounds. Rocq: `bvToNat_bvNat`. -/
theorem bvToNat_bvNat (w n : Nat) :
    n < 2^w → bvToNat w (bvNat w n) = n := by
  intro h
  unfold bvToNat bvNat
  rw [vecToBitVec_bitVecToVec, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- `bvToNat` is bounded by 2^w. Rocq: `bvToNat_bounds`. -/
theorem bvToNat_bounds (w : Nat) (x : Vec w Bool) :
    bvToNat w x < 2^w := by
  unfold bvToNat
  exact (vecToBitVec x).isLt

/-! ### Helpers for routing through `BitVec`

Phase 9: small helpers used by the successor/predecessor and
sign-bridge proofs below. Each is a `vecToBitVec` ∘ `intToBv`
or similar reduction that's a one-line proof but worth naming
to keep the downstream proofs readable. -/

/-- `vecToBitVec ∘ intToBv` is `BitVec.ofInt`. -/
theorem vecToBitVec_intToBv (w : Nat) (k : Int) :
    vecToBitVec (intToBv w k) = BitVec.ofInt w k := by
  unfold intToBv; rw [vecToBitVec_bitVecToVec]

/-- `vecToBitVec ∘ bvAdd` distributes over BitVec.add. -/
theorem vecToBitVec_bvAdd (w : Nat) (a b : Vec w Bool) :
    vecToBitVec (bvAdd w a b) = vecToBitVec a + vecToBitVec b := by
  unfold bvAdd; rw [vecToBitVec_bitVecToVec]

/-- `vecToBitVec ∘ bvSub` distributes over BitVec.sub. -/
theorem vecToBitVec_bvSub (w : Nat) (a b : Vec w Bool) :
    vecToBitVec (bvSub w a b) = vecToBitVec a - vecToBitVec b := by
  unfold bvSub; rw [vecToBitVec_bitVecToVec]

/-! Phase 9 / Case Study C: bv→BitVec bridges for the remaining
    bitwise/arithmetic primitives. These are mechanical
    `unfold + round-trip` proofs but they're load-bearing for
    checked proofs that move emitted SAW bitvectors into Lean's
    `BitVec` theory (Case C salsa20 quarterround surfaced their
    absence). Per the obvious-correctness principle (§2.4): the
    equivalences live in this Lean library
    as theorems, not as translator-side rewrites. -/

/-- `vecToBitVec ∘ bvShl` distributes over BitVec shift-left. -/
@[simp]
theorem vecToBitVec_bvShl (w : Nat) (a : Vec w Bool) (i : Nat) :
    vecToBitVec (bvShl w a i) = vecToBitVec a <<< i := by
  unfold bvShl; rw [vecToBitVec_bitVecToVec]

/-- `vecToBitVec ∘ bvShr` distributes over BitVec shift-right. -/
@[simp]
theorem vecToBitVec_bvShr (w : Nat) (a : Vec w Bool) (i : Nat) :
    vecToBitVec (bvShr w a i) = vecToBitVec a >>> i := by
  unfold bvShr; rw [vecToBitVec_bitVecToVec]

/-- `vecToBitVec ∘ bvSShr` distributes over BitVec arithmetic
shift-right. W2 seed (byte_add): the emitted carry extraction is
`bvSShr 31 x 8`; this moves it into `BitVec.sshiftRight`, where
`BitVec.sshiftRight_eq_of_msb_false` exchanges it for the logical
shift once the operand's sign bit is proven clear. -/
@[simp]
theorem vecToBitVec_bvSShr (w : Nat) (a : Vec (w + 1) Bool) (i : Nat) :
    vecToBitVec (bvSShr w a i) = (vecToBitVec a).sshiftRight i := by
  unfold bvSShr; rw [vecToBitVec_bitVecToVec]

/-- `vecToBitVec ∘ bvOr` distributes over BitVec OR. -/
@[simp]
theorem vecToBitVec_bvOr (w : Nat) (a b : Vec w Bool) :
    vecToBitVec (bvOr w a b) = vecToBitVec a ||| vecToBitVec b := by
  unfold bvOr; rw [vecToBitVec_bitVecToVec]

/-- `vecToBitVec ∘ bvXor` distributes over BitVec XOR. -/
@[simp]
theorem vecToBitVec_bvXor (w : Nat) (a b : Vec w Bool) :
    vecToBitVec (bvXor w a b) = vecToBitVec a ^^^ vecToBitVec b := by
  unfold bvXor; rw [vecToBitVec_bitVecToVec]

/-- `bvEq … = true` collapses to BitVec equality. Useful as a
    rewriting target for goals of the form `bvEq w a b = true`. -/
theorem bvEq_true_iff_BitVec_eq (w : Nat) (a b : Vec w Bool) :
    (bvEq w a b = true) ↔ (vecToBitVec a = vecToBitVec b) := by
  unfold bvEq
  simp

/-! ### vecToBitVec MSB-encoding lemma (Case Study C, 2026-05-05)

`vecToBitVec` reads a `Vec n Bool` MSB-first (position 0 is the
most-significant bit). Lean's `BitVec.ofBoolListBE` does the same on
`List Bool`. The encoding agreement gives us a getMsbD readback that
matches Vec's natural index — the missing piece for proving any
position-permuting bv operation (rotateL / rotateR / shiftL / shiftR /
reverse) bridges between Vec-land and BitVec-land. -/

private theorem ofBoolListBE_cons_toNat (b : Bool) (rest : List Bool) :
    (BitVec.ofBoolListBE (b :: rest)).toNat
      = b.toNat * 2 ^ rest.length + (BitVec.ofBoolListBE rest).toNat := by
  show (BitVec.cons b (BitVec.ofBoolListBE rest)).toNat = _
  rw [BitVec.toNat_cons]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.ofBoolListBE rest).isLt b.toNat]
  rw [Nat.shiftLeft_eq]

private theorem vector_foldl_eq_list_foldl
    {α : Type} {n : Nat} (v : Vector α n) (f : Nat → α → Nat) (b : Nat) :
    Vector.foldl f b v = List.foldl f b v.toList := by
  unfold Vector.foldl Vector.toList
  rw [← Array.foldl_toList]

private theorem foldl_acc_eq_ofBoolListBE_toNat
    (l : List Bool) (acc : Nat) :
    l.foldl (fun a b => 2 * a + b.toNat) acc =
      acc * 2 ^ l.length + (BitVec.ofBoolListBE l).toNat := by
  induction l generalizing acc with
  | nil => simp [BitVec.ofBoolListBE]
  | cons b rest ih =>
    -- Goal RHS has `(BitVec.ofBoolListBE (b :: rest)).toNat`. Direct
    -- `rw [hcons]` fails on dependent-type motive abstraction (the
    -- BitVec width depends on `(b :: rest).length`). Work around by
    -- unfolding to `BitVec.cons` first via `show`, which is
    -- definitionally equal — that side-steps the motive issue.
    show List.foldl (fun a b => 2 * a + b.toNat) (2 * acc + b.toNat) rest
        = acc * 2 ^ (rest.length + 1)
            + (BitVec.cons b (BitVec.ofBoolListBE rest)).toNat
    rw [ih (2 * acc + b.toNat), BitVec.toNat_cons,
        ← Nat.shiftLeft_add_eq_or_of_lt
          (BitVec.ofBoolListBE rest).isLt b.toNat,
        Nat.shiftLeft_eq]
    have h : acc * 2 ^ (rest.length + 1) = (2 * acc) * 2 ^ rest.length := by
      rw [Nat.pow_succ]; ac_rfl
    rw [h, Nat.add_mul, Nat.add_assoc]

theorem vecToBitVec_eq_ofBoolListBE_cast {n : Nat} (v : Vec n Bool) :
    vecToBitVec v
      = (BitVec.ofBoolListBE v.toList).cast Vector.length_toList := by
  apply BitVec.eq_of_toNat_eq
  unfold vecToBitVec
  rw [BitVec.toNat_ofNat, BitVec.toNat_cast]
  rw [vector_foldl_eq_list_foldl]
  rw [foldl_acc_eq_ofBoolListBE_toNat v.toList 0]
  simp only [Nat.zero_mul, Nat.zero_add]
  -- Goal: (BitVec.ofBoolListBE v.toList).toNat % 2^n = (BitVec.ofBoolListBE v.toList).toNat
  apply Nat.mod_eq_of_lt
  -- isLt gives `... < 2^v.toList.length`; need `... < 2^n`. Avoid the
  -- dependent-type motive by routing through `Nat.lt_of_lt_of_eq`.
  exact Nat.lt_of_lt_of_eq (BitVec.ofBoolListBE v.toList).isLt
    (congrArg (2 ^ ·) Vector.length_toList)

/-- The headline lemma: reading the i-th MSB of `vecToBitVec v` agrees
with the i-th element of `v.toList`. -/
theorem getMsbD_vecToBitVec {n : Nat} (v : Vec n Bool) (i : Nat) :
    (vecToBitVec v).getMsbD i = v.toList.getD i false := by
  rw [vecToBitVec_eq_ofBoolListBE_cast]
  simp [BitVec.getMsbD_ofBoolListBE]

/-- Cleanly indexed form: `(vecToBitVec v).getMsbD i = v[i]` for `i < n`. -/
theorem getMsbD_vecToBitVec_lt {n : Nat} (v : Vec n Bool) (i : Nat) (h : i < n) :
    (vecToBitVec v).getMsbD i = v[i] := by
  have hlen : i < v.toList.length := by rw [Vector.length_toList]; exact h
  rw [getMsbD_vecToBitVec]
  rw [← List.getElem_eq_getD (h := hlen) false]
  exact Vector.getElem_toList hlen

/-! ### vecToBitVec ∘ rotateL bridge (Case Study C, 2026-05-05)

The rotateL primitive's modular indexing matches BitVec.rotateLeft
exactly when both are interpreted MSB-first. Reduces SAW's `<<<`
emission to a direct Lean `BitVec` expression that checked lemmas and
tactics can reason about. -/

@[simp]
theorem vecToBitVec_rotateL (n : Nat) (x : Vec n Bool) (k : Nat) :
    vecToBitVec (rotateL n Bool x k) = (vecToBitVec x).rotateLeft k := by
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  rw [getMsbD_vecToBitVec_lt _ _ hi]
  rw [BitVec.getMsbD_rotateLeft]
  simp only [hi, decide_true, Bool.true_and]
  rw [getMsbD_vecToBitVec_lt _ _ (Nat.mod_lt _ (Nat.zero_lt_of_lt hi))]
  unfold rotateL
  simp [Vector.getElem_ofFn, Nat.add_comm]

/-- `BitVec.ofInt w 1 = 1#w` (small numeric coercion). -/
theorem BitVec_ofInt_one (w : Nat) : (BitVec.ofInt w 1 : BitVec w) = 1#w := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `BitVec.ofInt w 0 = 0#w`. -/
theorem BitVec_ofInt_zero (w : Nat) : (BitVec.ofInt w 0 : BitVec w) = 0#w := by
  apply BitVec.eq_of_toInt_eq; simp

/-! ### Successor/predecessor lemmas (Phase 9)

These chain bv comparisons with `bvAdd w _ (intToBv w 1)` /
`bvSub w _ (intToBv w 1)` neighbors. Rocq proves via 3-bit
exhaustion; we prove via `BitVec.toNat` / `toInt` reasoning. -/

/-- Strict-less plus 1 ≤ — unsigned. Rocq: `isBvult_to_isBvule_suc`. -/
theorem isBvult_to_isBvule_suc (w : Nat) (a b : Vec w Bool) :
    isBvult w a b → isBvule w (bvAdd w a (intToBv w 1)) b := by
  intro h
  unfold isBvult isBvule bvult bvule at *
  rw [vecToBitVec_bvAdd, vecToBitVec_intToBv]
  rw [BitVec.ult] at h
  rw [BitVec.ule, BitVec_ofInt_one, BitVec.toNat_add]
  simp at h
  refine decide_eq_true ?_
  show ((vecToBitVec a).toNat + (1 : BitVec w).toNat) % 2 ^ w ≤ (vecToBitVec b).toNat
  have hbb : (vecToBitVec b).toNat < 2^w := (vecToBitVec b).isLt
  have htn1 : ((1 : BitVec w)).toNat ≤ 1 := Nat.mod_le _ _
  have := Nat.mod_le ((vecToBitVec a).toNat + (1 : BitVec w).toNat) (2^w)
  omega

private theorem two_pow_pred_int (w : Nat) (hw : 1 ≤ w) :
    2 * (2 : Int)^(w - 1) = 2^w := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0) with ⟨w', rfl⟩
  simp
  rw [Int.pow_succ, Int.mul_comm]

/-- Strict-less plus 1 ≤ — signed. Rocq: `isBvslt_to_isBvsle_suc`. -/
theorem isBvslt_to_isBvsle_suc (w : Nat) (a b : Vec w Bool) :
    isBvslt w a b → isBvsle w (bvAdd w a (intToBv w 1)) b := by
  intro h
  unfold isBvslt isBvsle bvslt bvsle at *
  rw [vecToBitVec_bvAdd, vecToBitVec_intToBv]
  rw [BitVec.slt] at h
  rw [BitVec.sle, BitVec_ofInt_one]
  refine decide_eq_true ?_
  rw [BitVec.toInt_add]
  simp at h
  have hxle := BitVec.toInt_le (x := vecToBitVec a) (w := w)
  have hxbot := BitVec.toInt_intMin_le (vecToBitVec a)
  have hyle := BitVec.toInt_le (x := vecToBitVec b) (w := w)
  have hybot := BitVec.toInt_intMin_le (vecToBitVec b)
  rw [BitVec.toInt_intMin] at hxbot hybot
  rcases Nat.lt_or_ge 1 w with hw | hw
  · rw [BitVec.toInt_one hw]
    have hwpow : (2 : Nat)^(w-1) % 2^w = 2^(w-1) :=
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
    rw [hwpow] at hxbot hybot
    have h2eq : 2 * (2 : Int)^(w-1) = 2^w := two_pow_pred_int w (by omega)
    have h2pos : (0 : Int) < 2^(w-1) := by
      have : (0 : Nat) < 2^(w-1) := Nat.two_pow_pos (w-1)
      exact_mod_cast this
    have hmod : ((vecToBitVec a).toInt + 1).bmod (2^w) = (vecToBitVec a).toInt + 1 := by
      apply Int.bmod_eq_of_le_mul_two <;> push_cast at * <;> omega
    rw [hmod]; push_cast at *; omega
  · rcases Nat.eq_zero_or_pos w with hw0 | hw1
    · subst hw0; simp at hxle hxbot hyle hybot; omega
    · have heq : w = 1 := by omega
      subst heq
      have h1 : (1#1).toInt = -1 := by decide
      rw [h1]
      simp at hxle hxbot hyle hybot
      have ha : (vecToBitVec a).toInt = -1 := by omega
      have hb : (vecToBitVec b).toInt = 0 := by omega
      rw [ha, hb]; decide

/-- Successor preserves signed less-or-equal when below bvsmax.
Rocq: `isBvsle_suc_r`. -/
theorem isBvsle_suc_r (w : Nat) (a : Vec w Bool) :
    isBvslt w a (bvsmax w) → isBvsle w a (bvAdd w a (intToBv w 1)) := by
  intro h
  unfold isBvslt isBvsle bvslt bvsle bvsmax at *
  rw [vecToBitVec_bvAdd, vecToBitVec_intToBv]
  rw [BitVec.slt, vecToBitVec_bitVecToVec, BitVec.toInt_intMax] at h
  rw [BitVec.sle, BitVec_ofInt_one]
  refine decide_eq_true ?_
  rw [BitVec.toInt_add]
  simp at h
  have hxle := BitVec.toInt_le (x := vecToBitVec a) (w := w)
  have hxbot := BitVec.toInt_intMin_le (vecToBitVec a)
  rw [BitVec.toInt_intMin] at hxbot
  rcases Nat.lt_or_ge 1 w with hw | hw
  · rw [BitVec.toInt_one hw]
    have hwpow : (2 : Nat)^(w-1) % 2^w = 2^(w-1) :=
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
    rw [hwpow] at hxbot
    have h2eq : 2 * (2 : Int)^(w-1) = 2^w := two_pow_pred_int w (by omega)
    have h2pos : (0 : Int) < 2^(w-1) := by
      have : (0 : Nat) < 2^(w-1) := Nat.two_pow_pos (w-1); exact_mod_cast this
    have hmod : ((vecToBitVec a).toInt + 1).bmod (2^w) = (vecToBitVec a).toInt + 1 := by
      apply Int.bmod_eq_of_le_mul_two <;> push_cast at * <;> omega
    rw [hmod]; push_cast at *; omega
  · rcases Nat.eq_zero_or_pos w with hw0 | hw1
    · subst hw0; simp at hxle hxbot h; omega
    · have heq : w = 1 := by omega
      subst heq
      have h1 : (1#1).toInt = -1 := by decide
      rw [h1]
      simp at hxle hxbot h
      -- isBvslt w a bvsmax (= 0) means a.toInt < 0, so a.toInt = -1.
      have ha : (vecToBitVec a).toInt = -1 := by omega
      rw [ha]; decide

/-- Successor preserves signed strict-less. Rocq: `isBvslt_suc_r`. -/
theorem isBvslt_suc_r (w : Nat) (a : Vec w Bool) :
    isBvslt w a (bvsmax w) → isBvslt w a (bvAdd w a (intToBv w 1)) := by
  intro h
  unfold isBvslt bvslt bvsmax at *
  rw [vecToBitVec_bvAdd, vecToBitVec_intToBv]
  rw [BitVec.slt, vecToBitVec_bitVecToVec, BitVec.toInt_intMax] at h
  rw [BitVec.slt, BitVec_ofInt_one]
  refine decide_eq_true ?_
  rw [BitVec.toInt_add]
  simp at h
  have hxle := BitVec.toInt_le (x := vecToBitVec a) (w := w)
  have hxbot := BitVec.toInt_intMin_le (vecToBitVec a)
  rw [BitVec.toInt_intMin] at hxbot
  rcases Nat.lt_or_ge 1 w with hw | hw
  · rw [BitVec.toInt_one hw]
    have hwpow : (2 : Nat)^(w-1) % 2^w = 2^(w-1) :=
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
    rw [hwpow] at hxbot
    have h2eq : 2 * (2 : Int)^(w-1) = 2^w := two_pow_pred_int w (by omega)
    have h2pos : (0 : Int) < 2^(w-1) := by
      have : (0 : Nat) < 2^(w-1) := Nat.two_pow_pos (w-1); exact_mod_cast this
    have hmod : ((vecToBitVec a).toInt + 1).bmod (2^w) = (vecToBitVec a).toInt + 1 := by
      apply Int.bmod_eq_of_le_mul_two <;> push_cast at * <;> omega
    rw [hmod]; push_cast at *; omega
  · rcases Nat.eq_zero_or_pos w with hw0 | hw1
    · subst hw0; simp at hxle hxbot h; omega
    · have heq : w = 1 := by omega
      subst heq
      have h1 : (1#1).toInt = -1 := by decide
      rw [h1]
      simp at hxle hxbot h
      have ha : (vecToBitVec a).toInt = -1 := by omega
      rw [ha]; decide

/-- Predecessor preserves signed strict-less when above bvsmin.
Rocq: `isBvslt_pred_l`. -/
theorem isBvslt_pred_l (w : Nat) (a : Vec w Bool) :
    isBvslt w (bvsmin w) a → isBvslt w (bvSub w a (intToBv w 1)) a := by
  intro h
  unfold isBvslt bvslt bvsmin at *
  rw [vecToBitVec_bvSub, vecToBitVec_intToBv]
  rw [BitVec.slt, vecToBitVec_bitVecToVec] at h
  rw [BitVec.slt, BitVec_ofInt_one]
  refine decide_eq_true ?_
  rw [BitVec.toInt_sub]
  simp at h
  have hxle := BitVec.toInt_le (x := vecToBitVec a) (w := w)
  have hxbot := BitVec.toInt_intMin_le (vecToBitVec a)
  rw [BitVec.toInt_intMin] at hxbot h
  rcases Nat.lt_or_ge 1 w with hw | hw
  · rw [BitVec.toInt_one hw]
    have hwpow : (2 : Nat)^(w-1) % 2^w = 2^(w-1) :=
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
    rw [hwpow] at hxbot h
    have h2eq : 2 * (2 : Int)^(w-1) = 2^w := two_pow_pred_int w (by omega)
    have h2pos : (0 : Int) < 2^(w-1) := by
      have : (0 : Nat) < 2^(w-1) := Nat.two_pow_pos (w-1); exact_mod_cast this
    have hmod : ((vecToBitVec a).toInt - 1).bmod (2^w) = (vecToBitVec a).toInt - 1 := by
      apply Int.bmod_eq_of_le_mul_two <;> push_cast at * <;> omega
    rw [hmod]; push_cast at *; omega
  · rcases Nat.eq_zero_or_pos w with hw0 | hw1
    · subst hw0; simp at hxle hxbot h; omega
    · have heq : w = 1 := by omega
      subst heq
      have h1 : (1#1).toInt = -1 := by decide
      rw [h1]
      simp at hxle hxbot h
      have ha : (vecToBitVec a).toInt = 0 := by omega
      rw [ha]; decide

/-- Predecessor preserves signed less-or-equal. Rocq: `isBvsle_pred_l`. -/
theorem isBvsle_pred_l (w : Nat) (a : Vec w Bool) :
    isBvslt w (bvsmin w) a → isBvsle w (bvSub w a (intToBv w 1)) a := by
  intro h
  unfold isBvslt isBvsle bvslt bvsle bvsmin at *
  rw [vecToBitVec_bvSub, vecToBitVec_intToBv]
  rw [BitVec.slt, vecToBitVec_bitVecToVec] at h
  rw [BitVec.sle, BitVec_ofInt_one]
  refine decide_eq_true ?_
  rw [BitVec.toInt_sub]
  simp at h
  have hxle := BitVec.toInt_le (x := vecToBitVec a) (w := w)
  have hxbot := BitVec.toInt_intMin_le (vecToBitVec a)
  rw [BitVec.toInt_intMin] at hxbot h
  rcases Nat.lt_or_ge 1 w with hw | hw
  · rw [BitVec.toInt_one hw]
    have hwpow : (2 : Nat)^(w-1) % 2^w = 2^(w-1) :=
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
    rw [hwpow] at hxbot h
    have h2eq : 2 * (2 : Int)^(w-1) = 2^w := two_pow_pred_int w (by omega)
    have h2pos : (0 : Int) < 2^(w-1) := by
      have : (0 : Nat) < 2^(w-1) := Nat.two_pow_pos (w-1); exact_mod_cast this
    have hmod : ((vecToBitVec a).toInt - 1).bmod (2^w) = (vecToBitVec a).toInt - 1 := by
      apply Int.bmod_eq_of_le_mul_two <;> push_cast at * <;> omega
    rw [hmod]; push_cast at *; omega
  · rcases Nat.eq_zero_or_pos w with hw0 | hw1
    · subst hw0; simp at hxle hxbot h; omega
    · have heq : w = 1 := by omega
      subst heq
      have h1 : (1#1).toInt = -1 := by decide
      rw [h1]
      simp at hxle hxbot h
      have ha : (vecToBitVec a).toInt = 0 := by omega
      rw [ha]; decide

/-! ### Sign / unsigned bridge theorems

Phase 9: for non-negative bvs, signed and unsigned comparisons
agree. The two helpers `toInt_eq_toNat_of_nonneg` and
`toInt_eq_toNat_sub_of_neg` reduce signed reasoning to unsigned. -/

/-- When `0 ≤ x.toInt`, `x.toInt = x.toNat` (no sign-extension). -/
private theorem toInt_eq_toNat_of_nonneg (n : Nat) (x : BitVec n)
    (h : 0 ≤ x.toInt) : x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  split <;> omega

/-- When `x.toInt < 0`, `x.toInt = x.toNat - 2^n`. -/
private theorem toInt_eq_toNat_sub_of_neg (n : Nat) (x : BitVec n)
    (h : x.toInt < 0) : x.toInt = (x.toNat : Int) - (2 ^ n : Nat) := by
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  split at h
  · omega
  · split <;> omega

/-- Unsigned strict-less ↔ signed strict-less, when both
non-negative. Rocq: `isBvult_to_isBvslt_pos`. -/
theorem isBvult_to_isBvslt_pos (w : Nat) (a b : Vec w Bool) :
    isBvsle w (intToBv w 0) a → isBvsle w (intToBv w 0) b →
    (isBvult w a b ↔ isBvslt w a b) := by
  unfold isBvsle isBvslt isBvult bvsle bvslt bvult
  intros ha hb
  rw [BitVec.sle, vecToBitVec_intToBv, BitVec_ofInt_zero] at ha hb
  simp at ha hb
  have ha' := toInt_eq_toNat_of_nonneg _ _ ha
  have hb' := toInt_eq_toNat_of_nonneg _ _ hb
  rw [BitVec.ult, BitVec.slt, ha', hb']
  simp

/-- Unsigned less-or-equal ↔ signed less-or-equal, when both
non-negative. Rocq: `isBvule_to_isBvsle_pos`. -/
theorem isBvule_to_isBvsle_pos (w : Nat) (a b : Vec w Bool) :
    isBvsle w (intToBv w 0) a → isBvsle w (intToBv w 0) b →
    (isBvule w a b ↔ isBvsle w a b) := by
  unfold isBvsle isBvule bvsle bvule
  intros ha hb
  rw [BitVec.sle, vecToBitVec_intToBv, BitVec_ofInt_zero] at ha hb
  simp at ha hb
  have ha' := toInt_eq_toNat_of_nonneg _ _ ha
  have hb' := toInt_eq_toNat_of_nonneg _ _ hb
  rw [BitVec.ule, BitVec.sle, ha', hb']
  simp

/-- Unsigned-less and signed-negative propagates. Rocq:
`bvule_to_bvslt_zero`. -/
theorem bvule_to_bvslt_zero (w : Nat) (a b : Vec w Bool) :
    isBvule w a b → isBvslt w a (intToBv w 0) →
    isBvslt w b (intToBv w 0) := by
  unfold isBvule isBvslt bvule bvslt
  intros hule hslt
  rw [BitVec.ule] at hule
  rw [BitVec.slt, vecToBitVec_intToBv, BitVec_ofInt_zero] at hslt
  rw [BitVec.slt, vecToBitVec_intToBv, BitVec_ofInt_zero]
  simp at hule hslt ⊢
  -- a.toInt < 0 means 2*a.toNat ≥ 2^w; b.toNat ≥ a.toNat so 2*b.toNat ≥ 2^w;
  -- so b.toInt = b.toNat - 2^w; b.toNat < 2^w so b.toInt < 0.
  have hbn : (vecToBitVec b).toNat < 2^w := (vecToBitVec b).isLt
  rw [BitVec.toInt_eq_toNat_cond] at hslt ⊢
  split at hslt <;> split <;> omega

/-- Unsigned-less and non-negative propagates. Rocq:
`bvule_to_zero_bvsle`. -/
theorem bvule_to_zero_bvsle (w : Nat) (a b : Vec w Bool) :
    isBvule w a b → isBvsle w (intToBv w 0) b →
    isBvsle w (intToBv w 0) a := by
  unfold isBvule isBvsle bvule bvsle
  intros hule hsle
  rw [BitVec.ule] at hule
  rw [BitVec.sle, vecToBitVec_intToBv, BitVec_ofInt_zero] at hsle
  rw [BitVec.sle, vecToBitVec_intToBv, BitVec_ofInt_zero]
  simp at hule hsle ⊢
  -- 0 ≤ b.toInt means 2*b.toNat < 2^w; a.toNat ≤ b.toNat so 2*a.toNat < 2^w;
  -- so a.toInt = a.toNat ≥ 0.
  rw [BitVec.toInt_eq_toNat_cond] at hsle ⊢
  split at hsle <;> split <;> omega

/-! ### bvEq via bvSub theorems

Phase 9: equality test in bv land equals "subtract and check
zero"; provable from `BitVec.sub_eq_zero_iff_eq`. -/

/-- `a = b ↔ bvSub a b = 0`. Rocq: `bvEq_bvSub_l`. -/
theorem bvEq_bvSub_l (w : Nat) (a b : Vec w Bool) :
    a = b ↔ bvSub w a b = intToBv w 0 := by
  unfold bvSub intToBv
  have hzero : (BitVec.ofInt w 0 : BitVec w) = 0#w := by
    apply BitVec.eq_of_toInt_eq; simp
  rw [hzero]
  constructor
  · intro h
    rw [h, BitVec.sub_self]
  · intro h
    have e1 : vecToBitVec (bitVecToVec (vecToBitVec a - vecToBitVec b))
           = vecToBitVec (bitVecToVec 0#w) := congrArg _ h
    rw [vecToBitVec_bitVecToVec, vecToBitVec_bitVecToVec] at e1
    have hab : vecToBitVec a = vecToBitVec b := by
      have hh : vecToBitVec a - vecToBitVec b + vecToBitVec b
              = 0#w + vecToBitVec b := by rw [e1]
      simp [BitVec.sub_add_cancel] at hh
      exact hh
    have : bitVecToVec (vecToBitVec a) = bitVecToVec (vecToBitVec b) := congrArg _ hab
    rwa [bitVecToVec_vecToBitVec, bitVecToVec_vecToBitVec] at this

/-- `a = b ↔ 0 = bvSub b a`. Rocq: `bvEq_bvSub_r`. -/
theorem bvEq_bvSub_r (w : Nat) (a b : Vec w Bool) :
    a = b ↔ intToBv w 0 = bvSub w b a := by
  unfold bvSub intToBv
  have hzero : (BitVec.ofInt w 0 : BitVec w) = 0#w := by
    apply BitVec.eq_of_toInt_eq; simp
  rw [hzero]
  constructor
  · intro h
    rw [h, BitVec.sub_self]
  · intro h
    have e1 : vecToBitVec (bitVecToVec 0#w)
           = vecToBitVec (bitVecToVec (vecToBitVec b - vecToBitVec a)) := congrArg _ h
    rw [vecToBitVec_bitVecToVec, vecToBitVec_bitVecToVec] at e1
    have hab : vecToBitVec a = vecToBitVec b := by
      have hh : vecToBitVec b - vecToBitVec a + vecToBitVec a
              = 0#w + vecToBitVec a := by rw [← e1]
      simp [BitVec.sub_add_cancel] at hh
      exact hh.symm
    have : bitVecToVec (vecToBitVec a) = bitVecToVec (vecToBitVec b) := congrArg _ hab
    rwa [bitVecToVec_vecToBitVec, bitVecToVec_vecToBitVec] at this

/-! ### W2 byte-decomposition seeds (2026-07-16, byte_add discharge)

The `llvm_byte_add_eq` goal (mp_add_simple == a + b) decomposes a
32-bit add into zero-padded byte windows, per-byte `bvAdd`s with
`bvSShr` carries, and `bvShl`/`bvOr` reassembly. Emission expresses
every extraction as a `gen 32` tower whose pure characterization is a
`Vector.ofFn` with an `if`-guarded `atWithDefault` window; these
lemmas carry those ofFn forms into `Lean.BitVec` shift/mask images so
the arithmetic core can run on `BitVec 32`. MSB-first throughout: Vec
position 0 is the most-significant bit, so a window whose PAD occupies
positions `< p` zeroes the HIGH `p` bits' worth of positions and the
window value lands in the LOW `32 - p` bits. -/

/-- Indexing the all-zero bitvector gives `false` at every position.
The pure image of emission's `atRuntimeCheckedM _ (pure (bvNat n 0)) i`
zero-pad branches. -/
theorem getElem_bvNat_zero (n i : Nat) (h : i < n) :
    (bvNat n 0)[i] = false := by
  unfold bvNat bitVecToVec
  rw [Vector.getElem_ofFn]
  rw [BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_ofNat]
  simp

/-- MSB-first zero-padded window image: an ofFn vector that is zero at
positions `< p` and reads `v` at positions `K + (i - p)` from `p` on
packs to `(vecToBitVec v >>> (p - K)) &&& (2^(32-p) - 1)`.

Instances used by the byte_add discharge: `p = 24, K ∈ {24,16,8,0}`
(the four `zext8_32` byte extractions, mask `0xff`, shifts
`0/8/16/24`) and `p = 16, K = 16` (the fused truncate-to-16 /
zero-extend-back mask, `x &&& 0xFFFF`, shift 0). -/
theorem vecToBitVec_zeroPadWindow32 (v : Vec 32 Bool) (p K : Nat)
    (hp : p ≤ 32) (hKp : K ≤ p) :
    vecToBitVec (Vector.ofFn (fun i : Fin 32 =>
      if i.val < p then false
      else atWithDefault 32 Bool false v (K + (i.val - p))))
      = (vecToBitVec v >>> (p - K)) &&& BitVec.ofNat 32 (2 ^ (32 - p) - 1) := by
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  rw [CryptolToLean.SAWCoreBitvectorsProofs.getMsbD_vecToBitVec_lt _ _ hi]
  rw [Vector.getElem_ofFn]
  rw [BitVec.getMsbD_and, BitVec.getMsbD_ushiftRight]
  rw [BitVec.getMsbD_eq_getLsbD (BitVec.ofNat 32 (2 ^ (32 - p) - 1))]
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases hip : i < p
  · simp only [if_pos hip, hi, decide_true, Bool.true_and]
    have hmask : ¬ (31 - i < 32 - p) := by omega
    simp [hmask]
  · simp only [if_neg hip]
    have h1 : ¬ (i < p - K) := by omega
    have h2 : 31 - i < 32 - p := by omega
    have h3 : i - (p - K) < 32 := by omega
    have h5 : K + (i - p) < 32 := by omega
    have h6 : 32 - 1 - i < 32 := by omega
    simp only [hi, decide_true, Bool.true_and, h1, decide_false,
               Bool.not_false, h2, Bool.and_true]
    rw [CryptolToLean.SAWCoreBitvectorsProofs.getMsbD_vecToBitVec_lt _ _ h3]
    rw [CryptolToLean.SAWCorePreludeProofs.atWithDefault_lt _ _ _ h5]
    simp only [h6, decide_true, Bool.and_true,
               show K + (i - p) = i - (p - K) from by omega]

/-- MSB-first fused two-byte reassembly image: an ofFn vector that is
zero at positions `< 16`, reads byte `24..31` of `s1` at positions
`16..23` and byte `24..31` of `s0` at positions `24..31` packs to
`((s1 &&& 0xff) <<< 8) ||| (s0 &&& 0xff)` — i.e. `r1:r0` of the
byte_add carry chain, zero-extended to 32 bits. -/
theorem vecToBitVec_bytePack32 (s1 s0 : Vec 32 Bool) :
    vecToBitVec (Vector.ofFn (fun i : Fin 32 =>
      if i.val < 24 then
        (if i.val < 16 then false
         else atWithDefault 32 Bool false s1 (24 + (i.val - 16)))
      else atWithDefault 32 Bool false s0 (24 + (i.val - 24))))
      = ((vecToBitVec s1 &&& 255#32) <<< 8) ||| (vecToBitVec s0 &&& 255#32) := by
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  rw [CryptolToLean.SAWCoreBitvectorsProofs.getMsbD_vecToBitVec_lt _ _ hi,
      Vector.getElem_ofFn]
  rw [BitVec.getMsbD_or, BitVec.getMsbD_shiftLeft, BitVec.getMsbD_and,
      BitVec.getMsbD_and]
  rw [show (255#32) = BitVec.ofNat 32 (2 ^ (32 - 24) - 1) from rfl]
  rw [BitVec.getMsbD_eq_getLsbD (BitVec.ofNat 32 (2 ^ (32 - 24) - 1)),
      BitVec.getMsbD_eq_getLsbD (BitVec.ofNat 32 (2 ^ (32 - 24) - 1)),
      BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat,
      Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases h16 : i < 16
  · have hB : ¬ 31 - i < 8 := by omega
    simp only [if_pos (show i < 24 from by omega), if_pos h16]
    simp [hB]
    intros
    omega
  · by_cases h24 : i < 24
    · have hA : 31 - (i + 8) < 8 := by omega
      have hB : ¬ 31 - i < 8 := by omega
      have hs1 : i + 8 < 32 := by omega
      have hg : 24 + (i - 16) < 32 := by omega
      have h6 : 32 - 1 - (i + 8) < 32 := by omega
      simp only [if_pos h24, if_neg h16, hA, hB, decide_true, decide_false,
                 Bool.and_false, Bool.or_false, Bool.and_true, hs1,
                 Bool.true_and, hi]
      rw [CryptolToLean.SAWCoreBitvectorsProofs.getMsbD_vecToBitVec_lt _ _ hs1,
          CryptolToLean.SAWCorePreludeProofs.atWithDefault_lt _ _ _ hg]
      simp only [h6, decide_true, Bool.and_true,
                 show 24 + (i - 16) = i + 8 from by omega]
    · have hA : ¬ i + 8 < 32 := by omega
      have hB : 31 - i < 8 := by omega
      have hg : 24 + (i - 24) < 32 := by omega
      have h6 : 32 - 1 - i < 32 := by omega
      simp only [if_neg h24, hA, decide_false, Bool.false_and, hB,
                 decide_true, Bool.and_true, hi, Bool.true_and,
                 Bool.and_false, Bool.false_or]
      rw [CryptolToLean.SAWCoreBitvectorsProofs.getMsbD_vecToBitVec_lt _ _ hi,
          CryptolToLean.SAWCorePreludeProofs.atWithDefault_lt _ _ _ hg]
      simp only [h6, decide_true, Bool.and_true,
                 show 24 + (i - 24) = i from by omega]

-- Boolean truth-table theorems (Rocq's boolEqb_eq, and_bool_eq_true,
-- etc.) intentionally NOT mirrored here. They're properties of Lean's
-- stdlib `&&`/`||`/`!`, but SAW's Prelude bool ops emit as
-- `ite Bool a b Bool.false`-style chains in our translated output
-- (per the `leanOpaqueBuiltins` opacity policy + L-16's wrapper
-- routing). Lean's standalone `&&` doesn't surface in user-facing
-- SAW-translated goals, so theorems about it would be Lean-stdlib
-- trivia not actually useful for discharging SAW proofs. The
-- `iteDep_True` / `iteDep_False` / `ite_True` / `ite_False` simp
-- lemmas in `SAWCorePreludeExtra` cover the SAW-emitted Bool-elim
-- shape directly.

end CryptolToLean.SAWCoreBitvectorsProofs
