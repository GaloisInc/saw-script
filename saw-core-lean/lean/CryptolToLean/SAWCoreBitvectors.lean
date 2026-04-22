/-
`CryptolToLean.SAWCoreBitvectors` — bind SAWCore's `bitvector n` to
Lean's native `BitVec n`.

Mirrors `SAWCoreBitvectors.v` (Rocq side leans on `coq-bits`). The Lean
version is thin because `BitVec` is already in std with a rich API
(`BitVec.toNat`, bitwise ops, shifts, decidable equality, etc.).
-/

namespace CryptolToLean.SAWCoreBitvectors

/-- SAWCore's `bitvector n` is Lean std's `BitVec n`. -/
abbrev bitvector (n : Nat) : Type := BitVec n

/-- Convenience aliases for the common word sizes. -/
abbrev U8  : Type := BitVec 8
abbrev U16 : Type := BitVec 16
abbrev U32 : Type := BitVec 32
abbrev U64 : Type := BitVec 64

end CryptolToLean.SAWCoreBitvectors
