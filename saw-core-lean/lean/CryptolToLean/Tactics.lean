/-
`CryptolToLean.Tactics` — convenience tactics for discharging
goals about translator-emitted SAW Cryptol code.

Phase 7 / 2026-05-03. Each tactic is a thin wrapper around stdlib
tactics with a curated set of unfold lemmas. The point is
ergonomics: a user proving a Cryptol property doesn't want to
recite the SAW-side names every time.

For pattern-by-pattern guidance on which tactic to reach for,
see `doc/proof-cookbook.md`.
-/

import CryptolToLean.SAWCorePrimitives
import CryptolToLean.SAWCoreVectors
import CryptolToLean.SAWCorePreludeExtra
import CryptolToLean.SAWCorePrelude_proofs
import CryptolToLean.SAWCoreBitvectors_proofs

namespace CryptolToLean.Tactics

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

/-- `saw_bv` — close goals about concrete-input bv arithmetic.
Unfolds the bv ops and `bvNat`/`intToBv` constants, applies
round-trip rewrites, and runs `decide`.

Use for:
  `bvAdd 8 (bvNat 8 5) (bvNat 8 3) = bvNat 8 8`

For symbolic identities (e.g. `bvAdd 8 x y = bvAdd 8 y x`), use
the named theorems from `SAWCoreBitvectorsProofs` directly —
see the cookbook table. -/
macro "saw_bv" : tactic => `(tactic|
  simp [bvAdd, bvSub, bvMul, bvNeg, bvUDiv, bvURem, bvSDiv, bvSRem,
        bvShl, bvShr, bvSShr, bvNot, bvAnd, bvOr, bvXor,
        bvEq, bvult, bvule, bvugt, bvuge,
        bvslt, bvsle, bvsgt, bvsge,
        bvUExt, bvSExt, bvNat, bvToNat, intToBv, sbvToInt,
        vecToBitVec_bitVecToVec, bitVecToVec_vecToBitVec])

/-- `saw_unfold` — unfold the SAW-named primitives without trying
to close. Useful when you want to inspect the underlying `BitVec`
expression and proceed manually.

Implementation note: uses `simp only [...]` rather than `unfold ...`.
Lean's `unfold` tactic fails if any listed name is absent from the
goal; users almost never have all 30 bv ops in a single goal, so
the strict form is unusable. `simp only` skips rules whose head
isn't reachable, which gives the desired "unfold whatever's there"
behaviour. -/
macro "saw_unfold" : tactic => `(tactic|
  simp only [bvAdd, bvSub, bvMul, bvNeg, bvUDiv, bvURem, bvSDiv, bvSRem,
             bvShl, bvShr, bvSShr, bvNot, bvAnd, bvOr, bvXor,
             bvEq, bvult, bvule, bvugt, bvuge,
             bvslt, bvsle, bvsgt, bvsge,
             bvUExt, bvSExt, bvNat, bvToNat, intToBv, sbvToInt])

/-- `saw_to_bitvec` — `saw_unfold` plus the `vecToBitVec ∘
bitVecToVec` round-trip rewrite. Lifts a SAW-typed goal to a
pure `BitVec` goal so `bv_decide` / mathlib `BitVec` lemmas can
attack it. -/
macro "saw_to_bitvec" : tactic => `(tactic|
  saw_unfold
  <;> simp only [vecToBitVec_bitVecToVec, bitVecToVec_vecToBitVec])

end CryptolToLean.Tactics
