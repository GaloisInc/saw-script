/-
`CryptolToLean.SAWCoreVectors` — bind SAWCore's `Vec n a` to Lean's
`Vector`.

Mirrors `SAWCoreVectorsAsRocqVectors.v`. Thin wrapper: Lean std already
ships a usable `Vector` type, so most of this file is renaming and
convenience lemmas.
-/

namespace CryptolToLean.SAWCoreVectors

/-- SAWCore's `Vec n a` is Lean std's `Vector a n`. Note the argument
order flip (SAWCore puts the length first). -/
abbrev Vec (n : Nat) (α : Type) : Type := Vector α n

end CryptolToLean.SAWCoreVectors
