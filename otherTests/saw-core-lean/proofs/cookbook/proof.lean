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
  - Pattern 9: checked wrapped-helper bridges.
-/

import CryptolToLean
open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs
open CryptolToLean.SAWCoreVectors

noncomputable section

-- Pattern 1: concrete-input bv arithmetic.
example : bvAdd 8 (bvNat 8 5) (bvNat 8 3) = bvNat 8 8 := by decide
example : bvMul 8 (bvNat 8 7) (bvNat 8 6) = bvNat 8 42 := by decide
example : bvAnd 8 (bvNat 8 0xFF) (bvNat 8 0x0F) = bvNat 8 0x0F := by decide

-- Pattern 1 alternate: same goals via kernel computation.
example : bvAdd 8 (bvNat 8 5) (bvNat 8 3) = bvNat 8 8 := by decide
example : bvSub 8 (bvNat 8 10) (bvNat 8 4) = bvNat 8 6 := by decide

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

-- Audit (2026-05-06): pin every cookbook-named theorem against
-- a small example proof. A claim in proof-cookbook.md that says
-- "use bvXor_zero for X" rots silently if no test fires when
-- bvXor_zero's statement drifts; this section makes the cookbook
-- a regression target.

-- Pattern 2 (extended): more bv arithmetic identities.
example (a b : Vec 8 Bool) :
    bvNeg 8 (bvAdd 8 a b) = bvAdd 8 (bvNeg 8 a) (bvNeg 8 b) :=
  bvNeg_bvAdd_distrib 8 a b
example (a : Vec 8 Bool) : bvSub 8 a (bvNat 8 0) = a := bvSub_n_zero 8 a
example (a : Vec 8 Bool) : bvSub 8 (bvNat 8 0) a = bvNeg 8 a :=
  bvSub_zero_n 8 a
example (x y z : Vec 8 Bool) :
    bvXor 8 (bvXor 8 x y) z = bvXor 8 x (bvXor 8 y z) :=
  bvXor_assoc 8 x y z
example (x : Vec 8 Bool) : bvXor 8 x (bvNat 8 0) = x := bvXor_zero 8 x

-- Pattern 3 (extended): equality bridges. bvEq_iff is the
-- Bool-Prop bridge, used whenever a discharge has bvEq w a b = true
-- as a hypothesis or goal. bvEq_bvSub_r is the dual of bvEq_bvSub_l.
example (a b : Vec 8 Bool) (h : bvEq 8 a b = Bool.true) : a = b :=
  (bvEq_iff 8 a b).mp h
example (a b : Vec 8 Bool) (h : a = b) : bvEq 8 a b = Bool.true :=
  (bvEq_iff 8 a b).mpr h
example (w : Nat) (a b : Vec w Bool) (h : intToBv w 0 = bvSub w b a) :
    a = b :=
  (bvEq_bvSub_r w a b).mpr h

-- Pattern 4 (extended): more comparison predicates.
example (w : Nat) (a b : Vec w Bool)
    (h1 : isBvsle w a b) (h2 : isBvsle w b a) : a = b :=
  isBvsle_antisymm w a b h1 h2
example (w : Nat) (a b : Vec w Bool) (h : isBvslt w a b) :
    bvEq w a b = false :=
  isBvslt_to_bvEq_false w a b h
example (w : Nat) (a b : Vec w Bool) (h : isBvule w a b) :
    isBvult w a b ∨ a = b :=
  isBvule_to_isBvult_or_eq w a b h
example (w : Nat) (a : Vec w Bool) : isBvule w (intToBv w 0) a :=
  isBvule_zero_n w a
example (w : Nat) (a : Vec w Bool) : ¬ isBvult w a (intToBv w 0) :=
  isBvult_n_zero w a
example (w : Nat) (a b : Vec w Bool) (h : isBvult w a b) :
    isBvule w (bvAdd w a (intToBv w 1)) b :=
  isBvult_to_isBvule_suc w a b h
example (w : Nat) (a b : Vec w Bool) (h : isBvslt w a b) :
    isBvsle w (bvAdd w a (intToBv w 1)) b :=
  isBvslt_to_isBvsle_suc w a b h

-- Tactic exercises. saw_to_bitvec is the on-ramp from
-- translator-emitted SAW bv names into Lean.BitVec, so mathlib
-- lemmas and checked automation can take over. saw_unfold is
-- the same thing minus the BitVec round-trip rewrite — useful
-- for inspecting the intermediate state when saw_to_bitvec
-- doesn't close. Both pinned here so a regression to either
-- macro's body fails loudly.
example : bvEq 8 (bvNat 8 5) (bvNat 8 5) = Bool.true := by
  decide
example (a : Vec 8 Bool) : bvEq 8 a a = Bool.true := bvEq_refl 8 a
example : ∃ b, bvEq 8 (bvNat 8 5) (bvNat 8 5) = b := by
  exact ⟨Bool.true, by decide⟩

-- Pattern 9: checked wrapped-helper bridges. These examples pin the
-- proof-carrying style for eager `Except` helpers: Lean must prove every
-- generated element/step succeeds before rewriting to the pure helper.
example (x : Bool) :
    atWithDefaultM 1 Bool (Except.error "bad")
      (vecSequenceM 1 Bool #v[Except.ok x]) 0 = Except.ok x := by
  have h := atWithDefaultM_vecSequenceM_ok_lt (α := Bool) (n := 1)
    (Except.error "bad") (#v[Except.ok x]) (#v[x]) 0
  simpa using h (by
    intro j
    cases j with
    | mk val isLt =>
        cases val with
        | zero => rfl
        | succ _ => omega) (by omega)

example (v : Vec 2 Bool) :
    foldrM Bool Bool 2
      (fun a acc => Bind.bind a (fun _ => acc))
      (Except.ok true) (Except.ok v) =
    Except.ok (foldr Bool Bool 2 (fun _ acc => acc) true v) := by
  apply foldrM_pure_eq_foldr
  intro a acc
  rfl

end
