/-
Stress-test E6 (tier 3): popcount equivalence — fold-spec vs.
self-referential comprehension shape from Popcount.cry.

Source: otherTests/saw-core-lean/test_offline_lean_stress.E6_prove0.lean
Cryptol property:
  popCount_fold  : [4] -> [3]
  popCount_fold  bits = foldl (\acc b -> if b then acc + 1 else acc) 0 bits

  popCount_naive : [4] -> [3]
  popCount_naive bits = ic ! 0
    where ic : [5][3]
          ic = [0] # [ if elt then prev + 1 else prev
                     | elt <- bits | prev <- ic ]

  property eq bits = popCount_fold bits == popCount_naive bits

The emitted goal mixes:
  - foldl on the spec side (Lean-stdlib computable),
  - genFix on the naive side (Phase 5 BoundedVecFold lowering of
    the self-referential comprehension), wrapped in `Either.rec`
    over the negative-index flag for `! 0`.

## Discharge: width-4 decision, NOT yet inductive (stopgap)

The proof below decomposes `bits : Vec 4 Bool` into four named
booleans and finishes by `decide`. Both sides reduce to a concrete
3-bit value per case (16 cases total), so `decide` closes them.

This is a small-case witness — it does NOT scale. The principled
discharge would be a polymorphic-over-width inductive lemma
in the support library:

  theorem popCount_fold_eq_naive (n : Nat) (bits : Vec n Bool) :
    <foldl-form n bits> = <genFix-form n bits>

proved by induction on `n` via a single-step "popcount step"
lemma:

  step b acc = if b then acc + 1 else acc
  popCount_fold  (bits.snoc b) = step b (popCount_fold  bits)
  popCount_naive (bits.snoc b) = step b (popCount_naive bits)

Each per-width discharge would then be a one-line instantiation
(matching the E1 / E5 / E7 pattern, where the support-library
lemma already covers all widths).

The blocker: the `genFix` step-lemma for the Cryptol
comprehension shape requires a `genFix_snoc` characterization
that hasn't been built yet. Filed as a Phase 7 follow-up
(see the `Generalize E6 to inductive over width` task).

We keep this width-4 discharge to (a) confirm the SAW emission
is well-formed and reduces to a true equality on every case at
this width, and (b) hold the test slot until the inductive
form lands.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

theorem goal_closed : goal := by
  intro bits
  obtain ⟨arr, harr⟩ := bits
  match arr, harr with
  | ⟨[b0, b1, b2, b3]⟩, _ =>
    revert b0 b1 b2 b3
    decide
