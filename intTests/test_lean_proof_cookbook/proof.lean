/-
Pins the worked examples in `doc/proof-cookbook.md`. If a future
change to the support library or theorem names breaks any of
these, this test fails loud — and the cookbook needs to be
updated accordingly.

This test exercises:
  - Pattern 1: concrete-input bv arithmetic (`decide`).
  - Pattern 2: bv arithmetic identities (theorems by name).
  - Pattern 3: bv equality via subtraction.
  - Pattern 4: signed comparison predicates.
  - Pattern 5: `iteDep` collapse.
  - Pattern 8: `vecToBitVec` round-trip rewrites.
-/

import CryptolToLean
open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCoreVectors

noncomputable section

-- Pattern 1: concrete-input bv arithmetic.
example : bvAdd 8 (bvNat 8 5) (bvNat 8 3) = bvNat 8 8 := by decide
example : bvMul 8 (bvNat 8 7) (bvNat 8 6) = bvNat 8 42 := by decide
example : bvAnd 8 (bvNat 8 0xFF) (bvNat 8 0x0F) = bvNat 8 0x0F := by decide

-- Pattern 2: bv arithmetic identities.
example (x y : Vec 8 Bool) : bvAdd 8 x y = bvAdd 8 y x := bvAdd_comm 8 x y
example (x : Vec 8 Bool) : bvAdd 8 (bvNat 8 0) x = x := bvAdd_id_l 8 x
example (x : Vec 8 Bool) : bvAdd 8 x (bvNat 8 0) = x := bvAdd_id_r 8 x
example (x y z : Vec 8 Bool) :
    bvAdd 8 (bvAdd 8 x y) z = bvAdd 8 x (bvAdd 8 y z) :=
  bvAdd_assoc 8 x y z
example (x : Vec 8 Bool) : bvXor 8 x x = bvNat 8 0 := bvXor_same 8 x
example (x y : Vec 8 Bool) : bvXor 8 x y = bvXor 8 y x := bvXor_comm 8 x y
example (x y : Vec 8 Bool) :
    bvSub 8 x y = bvAdd 8 x (bvNeg 8 y) := bvSub_eq_bvAdd_neg 8 x y

-- Pattern 3: bv equality via subtraction.
example (w : Nat) (x y : Vec w Bool) (h : bvSub w x y = intToBv w 0) :
    x = y :=
  (bvEq_bvSub_l w x y).mpr h

-- Pattern 4: signed comparison predicates.
example (w : Nat) (a b : Vec w Bool) (h : isBvslt w a b) :
    isBvsle w a b :=
  isBvslt_to_isBvsle w a b h
example (w : Nat) (a b : Vec w Bool) (h : isBvult w a b) :
    isBvule w a b :=
  isBvult_to_isBvule w a b h
example (w : Nat) (a : Vec w Bool) : ¬ isBvslt w a a :=
  isBvslt_antirefl w a
example (w : Nat) (a b : Vec w Bool)
    (h1 : isBvule w a b) (h2 : isBvslt w a (intToBv w 0)) :
    isBvslt w b (intToBv w 0) :=
  bvule_to_bvslt_zero w a b h1 h2

-- Pattern 5: iteDep / ite collapse via @[simp].
example (fT fF : Bool) :
    CryptolToLean.SAWCorePreludeExtra.ite Bool true fT fF = fT := by simp
example (fT fF : Bool) :
    CryptolToLean.SAWCorePreludeExtra.ite Bool false fT fF = fF := by simp

-- Pattern 6: Bool case-split (the walkthrough pattern).
example (a b c : Bool) :
    (CryptolToLean.SAWCorePreludeExtra.ite Bool
       (CryptolToLean.SAWCorePreludeExtra.ite Bool a b Bool.false)
       Bool.true
       (CryptolToLean.SAWCorePreludeExtra.ite Bool a c Bool.false)) =
    (CryptolToLean.SAWCorePreludeExtra.ite Bool a
       (CryptolToLean.SAWCorePreludeExtra.ite Bool b Bool.true c)
       Bool.false) := by
  cases a <;> cases b <;> cases c <;> rfl

-- Pattern 8: vecToBitVec round-trip rewrites.
example (n : Nat) (bv : BitVec n) :
    vecToBitVec (bitVecToVec bv) = bv :=
  vecToBitVec_bitVecToVec bv
example (n : Nat) (v : Vec n Bool) :
    bitVecToVec (vecToBitVec v) = v :=
  bitVecToVec_vecToBitVec v

end
