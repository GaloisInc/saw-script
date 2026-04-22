/-
`CryptolToLean.SAWCoreScaffolding` — base bindings that map the
primitive types and constants of SAWCore to Lean 4 concepts.

Mirrors `saw-core-rocq/rocq/handwritten/CryptolToRocq/
SAWCoreScaffolding.v` with Lean-flavour definitions. Populated
incrementally as the Phase-1 SpecialTreatment table grows.
-/

namespace CryptolToLean.SAWCoreScaffolding

/-- SAWCore's `Bit` is Lean's `Bool`. -/
abbrev Bit : Type := Bool

end CryptolToLean.SAWCoreScaffolding
