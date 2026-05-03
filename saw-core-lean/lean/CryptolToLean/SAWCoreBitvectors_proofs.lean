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

end CryptolToLean.SAWCoreBitvectorsProofs
