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

/-- A type of "inhabited" types — SAWCore's `isort` flag marks a sort
whose inhabitants are reachable (i.e. a default value exists). The
translator injects `{Inh_a : Inhabited a}` implicits on binders whose
type carries this flag; in Lean 4 the core `Inhabited` type class fills
the same role, so this is just a re-export. -/
abbrev Inhabited (α : Type) : Type := _root_.Inhabited α

end CryptolToLean.SAWCoreScaffolding
