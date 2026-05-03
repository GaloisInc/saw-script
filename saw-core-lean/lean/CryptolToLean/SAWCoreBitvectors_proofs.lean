/-
`CryptolToLean.SAWCoreBitvectors_proofs` — axiomatic theorems
about the bv axioms in `CryptolToLean.SAWCorePrimitives`.

Phase 3b (P3-1). Mirrors the lemma set in
`saw-core-rocq/rocq/handwritten/CryptolToRocq/SAWCoreBitvectors.v`.

# Why these are axioms, not theorems

The bv operations on the Lean side (`bvAdd`, `bvEq`, `bvXor`, …)
are declared as opaque axioms in `SAWCorePrimitives.lean`. Lean
can't prove anything about their behaviour because we don't
expose a representation. The Rocq backend declares them against
a `BitVector` representation (a `Vector bool n`-style) where the
operations DO have bodies, and proves the lemmas below from that
representation.

We faithfully transport the proven results via axioms. Each
axiom below is annotated with a pointer to the Rocq theorem that
proves it; if a future Rocq audit invalidates one of those
proofs, the matching axiom here is also wrong — but visibly so,
not silently.

# Trust posture

These axioms are SAW's claims about what its primitives mean.
Same trust shape as `unsafeAssert`, `coerce`, and the bv axioms
themselves: SAW vouches for the semantics, we transport.

The strategic alternative is the `Lean.BitVec` binding (Phase 6
deferred decision). Once `bvAdd` is bound to `BitVec.add`, every
lemma here becomes a Mathlib / `Std.Tactic.BVDecide` theorem
rather than a SAW-side axiom. Until then, this file is the
proof-side scaffolding that lets users discharge translated
Cryptol goals.
-/

import CryptolToLean.SAWCorePrimitives
import CryptolToLean.SAWCoreVectors
import CryptolToLean.SAWCorePreludeExtra

namespace CryptolToLean.SAWCoreBitvectorsProofs

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

/-! ## Bool reduction lemmas (cheaper than going through bv) -/

/-- `Bool.not` involution. Proved by `cases` — Lean's stdlib
provides this; re-exported here for symmetry with the
SAW-named primitives our translator emits via SpecialTreatment. -/
theorem not_not (b : Bool) : !(!b) = b := by cases b <;> rfl

/-- `&&` commutativity. Proved by `cases`. -/
theorem and_comm (a b : Bool) : (a && b) = (b && a) := by
  cases a <;> cases b <;> rfl

/-- `&&` associativity. -/
theorem and_assoc (a b c : Bool) : ((a && b) && c) = (a && (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `||` commutativity. -/
theorem or_comm (a b : Bool) : (a || b) = (b || a) := by
  cases a <;> cases b <;> rfl

/-- `||` associativity. -/
theorem or_assoc (a b c : Bool) : ((a || b) || c) = (a || (b || c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Distributivity (the Cryptol property `test_offline_lean.t2`
exercises). -/
theorem and_or_distrib (a b c : Bool) :
    ((a && b) || (a && c)) = (a && (b || c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## Bitvector arithmetic axioms

Each `axiom` below mirrors a Rocq `Lemma` in
`SAWCoreBitvectors.v`. The Rocq proof discharges from the
`BitVector` representation. Citation in the axiom's docstring. -/

/-- `bvAdd` left-identity. Rocq: `bvAdd_id_l`. -/
axiom bvAdd_id_l (w : Nat) (a : Vec w Bool) : bvAdd w (bvNat w 0) a = a

/-- `bvAdd` right-identity. Rocq: `bvAdd_id_r`. -/
axiom bvAdd_id_r (w : Nat) (a : Vec w Bool) : bvAdd w a (bvNat w 0) = a

/-- `bvAdd` commutativity. Rocq: `bvAdd_comm`. -/
axiom bvAdd_comm (w : Nat) (a b : Vec w Bool) : bvAdd w a b = bvAdd w b a

/-- `bvAdd` associativity. Rocq: `bvAdd_assoc`. -/
axiom bvAdd_assoc (w : Nat) (a b c : Vec w Bool) :
    bvAdd w (bvAdd w a b) c = bvAdd w a (bvAdd w b c)

/-- `bvSub` right-zero. Rocq: `bvSub_n_zero`. -/
axiom bvSub_n_zero (w : Nat) (a : Vec w Bool) :
    bvSub w a (bvNat w 0) = a

/-- `bvSub` left-zero is negation. Rocq: `bvSub_zero_n`. -/
axiom bvSub_zero_n (w : Nat) (a : Vec w Bool) :
    bvSub w (bvNat w 0) a = bvNeg w a

/-- `bvNeg` distributes over `bvAdd`. Rocq: `bvNeg_bvAdd_distrib`. -/
axiom bvNeg_bvAdd_distrib (w : Nat) (a b : Vec w Bool) :
    bvNeg w (bvAdd w a b) = bvAdd w (bvNeg w a) (bvNeg w b)

/-- `bvSub` rewrites to `bvAdd` of negation. Rocq:
`bvSub_eq_bvAdd_neg`. -/
axiom bvSub_eq_bvAdd_neg (w : Nat) (a b : Vec w Bool) :
    bvSub w a b = bvAdd w a (bvNeg w b)

/-! ## Bitvector xor axioms -/

/-- `bvXor` of a value with itself is zero. Rocq: `bvXor_same`. -/
axiom bvXor_same (n : Nat) (x : Vec n Bool) :
    bvXor n x x = bvNat n 0

/-- `bvXor` zero-identity. Rocq: `bvXor_zero`. -/
axiom bvXor_zero (n : Nat) (x : Vec n Bool) :
    bvXor n x (bvNat n 0) = x

/-- `bvXor` associativity. Rocq: `bvXor_assoc`. -/
axiom bvXor_assoc (n : Nat) (x y z : Vec n Bool) :
    bvXor n (bvXor n x y) z = bvXor n x (bvXor n y z)

/-- `bvXor` commutativity. Rocq: `bvXor_comm`. -/
axiom bvXor_comm (n : Nat) (x y : Vec n Bool) :
    bvXor n x y = bvXor n y x

/-! ## Bitvector equality axioms

These axiomatize the connection between `bvEq` (returning a SAW
`Bool`) and Lean propositional equality. Without these, a user
can't translate "the SAW Bool result of bvEq" into Lean's `=`
relation (or vice-versa). Rocq's `bvEq_eq` and `bvEq_refl` cover
this — proven from the bitwise-zip representation. -/

/-- `bvEq` reflexivity: `bvEq w x x = true` for any x. Rocq:
`bvEq_refl`. -/
axiom bvEq_refl (w : Nat) (a : Vec w Bool) :
    bvEq w a a = Bool.true

/-- `bvEq` symmetry. Rocq: `bvEq_sym`. -/
axiom bvEq_sym (w : Nat) (a b : Vec w Bool) :
    bvEq w a b = bvEq w b a

/-- `bvEq` is decision: returns `true` iff propositionally equal.
Rocq: `bvEq_eq`. We split the iff into two implications so users
can pick a direction without double-applying. -/
axiom bvEq_iff (w : Nat) (a b : Vec w Bool) :
    bvEq w a b = Bool.true ↔ a = b

/-- One direction of `bvEq_iff`, in convenient `=>` form. -/
theorem bvEq_eq_true_imp_eq
    (w : Nat) (a b : Vec w Bool) :
    bvEq w a b = Bool.true → a = b :=
  fun h => (bvEq_iff w a b).mp h

/-- The other direction. -/
theorem eq_imp_bvEq_eq_true
    (w : Nat) (a b : Vec w Bool) :
    a = b → bvEq w a b = Bool.true :=
  fun h => h ▸ bvEq_refl w a

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
Rocq: `bvsmax`. Constructive via `gen`. -/
def bvsmax (w : Nat) : Vec w Bool :=
  gen w Bool (fun i => decide (i + 1 < w))

/-- Signed-min bv value: `1000...0` (top bit set, rest clear).
Rocq: `bvsmin`. -/
def bvsmin (w : Nat) : Vec w Bool :=
  gen w Bool (fun i => decide (i + 1 = w))

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

/-! ### Equivalences between Bool and Prop forms

The "_def" lemmas are Rocq's reflexivity proofs; ours are `rfl`
since the Prop wrappers unfold to the Bool equation by definition. -/

theorem isBvsle_def (w : Nat) (a b : Vec w Bool) :
    bvsle w a b = true ↔ isBvsle w a b := Iff.rfl
theorem isBvslt_def (w : Nat) (a b : Vec w Bool) :
    bvslt w a b = true ↔ isBvslt w a b := Iff.rfl
theorem isBvule_def (w : Nat) (a b : Vec w Bool) :
    bvule w a b = true ↔ isBvule w a b := Iff.rfl
theorem isBvult_def (w : Nat) (a b : Vec w Bool) :
    bvult w a b = true ↔ isBvult w a b := Iff.rfl

/-! ### Cross-comparison lemmas (axiomatic Rocq transposition)

Each axiom matches Rocq's same-named lemma. Rocq proves via
`holds_for_bits_up_to_3` (exhaustive 0/1/2/3-bit case analysis);
we transport the conclusion. -/

/-- Strict-less implies less-or-equal (signed). Rocq: `isBvslt_to_isBvsle`. -/
axiom isBvslt_to_isBvsle (w : Nat) (a b : Vec w Bool) :
    isBvslt w a b → isBvsle w a b

/-- Strict-less implies less-or-equal (unsigned). Rocq: `isBvult_to_isBvule`. -/
axiom isBvult_to_isBvule (w : Nat) (a b : Vec w Bool) :
    isBvult w a b → isBvule w a b

/-- Less-or-equal splits as strict-less or equal. Rocq:
`isBvule_to_isBvult_or_eq`. -/
axiom isBvule_to_isBvult_or_eq (w : Nat) (a b : Vec w Bool) :
    isBvule w a b → isBvult w a b ∨ a = b

/-- Strict-less implies bvEq is false (signed). Rocq:
`isBvslt_to_bvEq_false`. -/
axiom isBvslt_to_bvEq_false (w : Nat) (a b : Vec w Bool) :
    isBvslt w a b → bvEq w a b = false

/-- Strict-less implies bvEq is false (unsigned). Rocq:
`isBvult_to_bvEq_false`. -/
axiom isBvult_to_bvEq_false (w : Nat) (a b : Vec w Bool) :
    isBvult w a b → bvEq w a b = false

/-! ### Edge-case lemmas (axiomatic)

Boundary properties around `bvsmin` / `bvsmax` / `intToBv 0`.
Each Rocq counterpart is at the same name. -/

/-- Antireflexivity of strict-less (signed). Rocq: `isBvslt_antirefl`. -/
axiom isBvslt_antirefl (w : Nat) (a : Vec w Bool) :
    ¬ isBvslt w a a

/-- Antisymmetry of less-or-equal (signed). Rocq: `isBvsle_antisymm`. -/
axiom isBvsle_antisymm (w : Nat) (a b : Vec w Bool) :
    isBvsle w a b → isBvsle w b a → a = b

/-- Nothing is signed-less than `bvsmin`. Rocq: `not_isBvslt_bvsmin`. -/
axiom not_isBvslt_bvsmin (w : Nat) (a : Vec w Bool) :
    ¬ isBvslt w a (bvsmin w)

/-- `bvsmax` is signed-greatest. Rocq: `not_isBvslt_bvsmax`. -/
axiom not_isBvslt_bvsmax (w : Nat) (a : Vec w Bool) :
    ¬ isBvslt w (bvsmax w) a

/-- Zero is unsigned-min. Rocq: `isBvule_zero_n`. -/
axiom isBvule_zero_n (w : Nat) (a : Vec w Bool) :
    isBvule w (intToBv w 0) a

/-- The only thing unsigned-≤ zero is zero. Rocq: `isBvule_n_zero`. -/
axiom isBvule_n_zero (w : Nat) (a : Vec w Bool) :
    isBvule w a (intToBv w 0) ↔ a = intToBv w 0

/-- Nothing is unsigned-strict-less than zero. Rocq: `isBvult_n_zero`. -/
axiom isBvult_n_zero (w : Nat) (a : Vec w Bool) :
    ¬ isBvult w a (intToBv w 0)

/-! ### bv round-trip lemmas

`bvNat`/`bvToNat` round-trip; mirrors Rocq's `bvNat_bvToNat_id`. -/

/-- Round-tripping a bv through `bvToNat` and back gives the
original. Rocq: `bvNat_bvToNat_id`. -/
axiom bvNat_bvToNat_id (w : Nat) (a : Vec w Bool) :
    bvNat w (bvToNat w a) = a

/-- Converse round-trip: `bvNat → bvToNat → original Nat`,
provided the input is in-bounds. Rocq: `bvToNat_bvNat`. -/
axiom bvToNat_bvNat (w n : Nat) :
    n < 2^w → bvToNat w (bvNat w n) = n

/-- `bvToNat` is bounded by 2^w. Rocq: `bvToNat_bounds`. -/
axiom bvToNat_bounds (w : Nat) (x : Vec w Bool) :
    bvToNat w x < 2^w

/-! ### Successor/predecessor lemmas (axiomatic Rocq transposition)

These chain bv comparisons with `bvAdd w _ (intToBv w 1)` /
`bvSub w _ (intToBv w 1)` neighbors. Rocq proves via 3-bit
exhaustion. -/

/-- Strict-less plus 1 ≤ — signed. Rocq: `isBvslt_to_isBvsle_suc`. -/
axiom isBvslt_to_isBvsle_suc (w : Nat) (a b : Vec w Bool) :
    isBvslt w a b → isBvsle w (bvAdd w a (intToBv w 1)) b

/-- Strict-less plus 1 ≤ — unsigned. Rocq: `isBvult_to_isBvule_suc`. -/
axiom isBvult_to_isBvule_suc (w : Nat) (a b : Vec w Bool) :
    isBvult w a b → isBvule w (bvAdd w a (intToBv w 1)) b

/-- Predecessor preserves signed strict-less when above bvsmin.
Rocq: `isBvslt_pred_l`. -/
axiom isBvslt_pred_l (w : Nat) (a : Vec w Bool) :
    isBvslt w (bvsmin w) a → isBvslt w (bvSub w a (intToBv w 1)) a

/-- Predecessor preserves signed less-or-equal. Rocq: `isBvsle_pred_l`. -/
axiom isBvsle_pred_l (w : Nat) (a : Vec w Bool) :
    isBvslt w (bvsmin w) a → isBvsle w (bvSub w a (intToBv w 1)) a

/-- Successor preserves signed less-or-equal when below bvsmax.
Rocq: `isBvsle_suc_r`. -/
axiom isBvsle_suc_r (w : Nat) (a : Vec w Bool) :
    isBvslt w a (bvsmax w) → isBvsle w a (bvAdd w a (intToBv w 1))

/-- Successor preserves signed strict-less. Rocq: `isBvslt_suc_r`. -/
axiom isBvslt_suc_r (w : Nat) (a : Vec w Bool) :
    isBvslt w a (bvsmax w) → isBvslt w a (bvAdd w a (intToBv w 1))

/-! ### Sign / unsigned bridge lemmas

For non-negative bvs, signed and unsigned comparisons agree. -/

/-- Unsigned strict-less ↔ signed strict-less, when both
non-negative. Rocq: `isBvult_to_isBvslt_pos`. -/
axiom isBvult_to_isBvslt_pos (w : Nat) (a b : Vec w Bool) :
    isBvsle w (intToBv w 0) a → isBvsle w (intToBv w 0) b →
    (isBvult w a b ↔ isBvslt w a b)

/-- Unsigned less-or-equal ↔ signed less-or-equal, when both
non-negative. Rocq: `isBvule_to_isBvsle_pos`. -/
axiom isBvule_to_isBvsle_pos (w : Nat) (a b : Vec w Bool) :
    isBvsle w (intToBv w 0) a → isBvsle w (intToBv w 0) b →
    (isBvule w a b ↔ isBvsle w a b)

/-- Unsigned-less and signed-negative propagates. Rocq:
`bvule_to_bvslt_zero`. -/
axiom bvule_to_bvslt_zero (w : Nat) (a b : Vec w Bool) :
    isBvule w a b → isBvslt w a (intToBv w 0) →
    isBvslt w b (intToBv w 0)

/-- Unsigned-less and non-negative propagates. Rocq:
`bvule_to_zero_bvsle`. -/
axiom bvule_to_zero_bvsle (w : Nat) (a b : Vec w Bool) :
    isBvule w a b → isBvsle w (intToBv w 0) b →
    isBvsle w (intToBv w 0) a

/-! ### bvEq via bvSub

Equality test in bv land equals "subtract and check zero". -/

/-- `a = b ↔ bvSub a b = 0`. Rocq: `bvEq_bvSub_l`. -/
axiom bvEq_bvSub_l (w : Nat) (a b : Vec w Bool) :
    a = b ↔ bvSub w a b = intToBv w 0

/-- `a = b ↔ 0 = bvSub b a`. Rocq: `bvEq_bvSub_r`. -/
axiom bvEq_bvSub_r (w : Nat) (a b : Vec w Bool) :
    a = b ↔ intToBv w 0 = bvSub w b a

/-! ### Boolean truth-table theorems

These lift Rocq's `boolEqb_*` / `and_bool_eq_*` / `or_bool_eq_*` /
`not_bool_eq_*` lemmas. Provable in Lean by `cases <;> rfl` since
they enumerate the four truth-table cases. -/

/-- Lean's `==` on Bool is propositional equality (true iff equal). -/
theorem bool_beq_eq (a b : Bool) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> simp

/-- Lean's `==` on Bool is propositional inequality (false iff distinct). -/
theorem bool_beq_neq (a b : Bool) : (a == b) = false ↔ a ≠ b := by
  cases a <;> cases b <;> simp

/-- Boolean and: `a && b = true ↔ a = true ∧ b = true`. -/
theorem and_bool_eq_true (a b : Bool) :
    (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

/-- Boolean and: `a && b = false ↔ a = false ∨ b = false`. -/
theorem and_bool_eq_false (a b : Bool) :
    (a && b) = false ↔ a = false ∨ b = false := by
  cases a <;> cases b <;> simp

/-- Boolean or: `a || b = true ↔ a = true ∨ b = true`. -/
theorem or_bool_eq_true (a b : Bool) :
    (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp

/-- Boolean or: `a || b = false ↔ a = false ∧ b = false`. -/
theorem or_bool_eq_false (a b : Bool) :
    (a || b) = false ↔ a = false ∧ b = false := by
  cases a <;> cases b <;> simp

/-- Boolean negation true. -/
theorem not_bool_eq_true (a : Bool) : (!a) = true ↔ a = false := by
  cases a <;> simp

/-- Boolean negation false. -/
theorem not_bool_eq_false (a : Bool) : (!a) = false ↔ a = true := by
  cases a <;> simp

end CryptolToLean.SAWCoreBitvectorsProofs
