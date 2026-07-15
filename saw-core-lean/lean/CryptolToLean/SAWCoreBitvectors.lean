/-
`CryptolToLean.SAWCoreBitvectors` — bind SAWCore's `bitvector n` to
its literal SAW semantics: a vector of `n` booleans.

SAWCore defines `bitvector n := Vec n Bool` in Prelude.sawcore. An
earlier draft aliased this to Lean's native `BitVec n` for
ergonomics, but `BitVec n` and `Vec n Bool` are semantically
distinct types (packed word vs. list of bits; indexing conventions
differ, eliminators differ, bitwise ops aren't definitionally equal
to their `List Bool` counterparts). That would have made Lean-side
proofs say something different from the SAWCore source — a
soundness violation.

That coherence layer LANDED (Phase 9): `vecToBitVec` /
`bitVecToVec` in `SAWCorePrimitives.lean` bridge the two types, the
`bv*` operations route through native `BitVec` via that round trip,
and the two round-trip axioms are the documented trusted base. The
`bitvector` TYPE itself deliberately remains `Vec n Bool` for source
fidelity.

The decision to keep `Vec n Bool` (rather than bind directly to
`Lean.BitVec n`) is documented at length in
`doc/2026-05-01_bitvec-binding-decision.md`, which lists the
trade-off and the conditions under which to revisit.
-/

import CryptolToLean.SAWCoreVectors

namespace CryptolToLean.SAWCoreBitvectors

/-- SAWCore's `bitvector n := Vec n Bool`. -/
abbrev bitvector (n : Nat) : Type :=
  CryptolToLean.SAWCoreVectors.Vec n Bool

end CryptolToLean.SAWCoreBitvectors
