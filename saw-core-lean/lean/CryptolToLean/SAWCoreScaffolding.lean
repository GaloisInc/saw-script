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
translator injects `[Inh_a : Inhabited a]` instance binders on
binders whose type carries this flag. This is universe-polymorphic
to match SAWCore, which uses `isort` at any sort level; Lean's own
`_root_.Inhabited` is restricted to `Type` and so is not a drop-in
substitute.

We model it as an unconstrained class so the generated preludes
elaborate; real proofs about Cryptol specs will typically supply
an instance via `default`/`arbitrary`. -/
class Inhabited.{u} (α : Sort u) : Type u where
  default : α

/-- Bridge from Lean's core `Inhabited`: any `α : Type` that Lean
already considers inhabited can supply our class's `default` by
delegation. -/
instance {α : Type} [_root_.Inhabited α] : Inhabited α where
  default := _root_.Inhabited.default

end CryptolToLean.SAWCoreScaffolding
