/-
Proof gap: ChaCha20 round-folding demo.

This file is preserved as a stress proof attempt, not an accepted backend proof
regression. The proof is axiom-clean in intent, but it currently exceeds the
practical elaboration/heartbeat budget under the default harness. It should
move back to `proofs/` only after the generated terms or proof script are
factored enough to check reliably without heartbeat inflation.

Lean discharge for the Cryptol-only
`core x == core x` reflexive equality.

The driver translates `core : Round -> Block` from
`deps/cryptol-specs/.../chacha20.cry`. After `scNormalizeForLean`
the goal contains a `cryptolIterate (Vec 16 (Vec 32 Bool)) cdround x`
emission — direct evidence the polymorphic-iterate translator
extension fired (without it the prove_print errored with "Refusing
to translate primitive fix").

The emitted goal compares the LLVM-style 64-byte block element-wise:
  `foldr ∧ true (gen 64 Bool (\i -> bvEq 8 byte_i byte_i)) = true`.
For each i ∈ [0, 64) the byte expression on each side of `bvEq` is
the same `let`-bound subterm, so `bvEq_refl` closes per-position
and the parametric `foldr_and_gen_eq_true_of_all` composes them.

Why this discharge matters: it pins that the entire 322-line `core`
emission — the 10-step `iterate cdround` lowered to `cryptolIterate`
+ `Stream.rec`, the byte-packing `blocked`, the state-add — yields
a Lean term for which equality decides. Anything that breaks the
iterate lowering (or the Pi/Lambda let-sharing that keeps it bounded)
tears this regression.
-/

import Emitted

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs
open CryptolToLean.SAWCorePreludeExtra

theorem goal_closed : goal := by
  intro x
  apply foldr_and_gen_eq_true_of_all 64
  intro i hi
  exact bvEq_refl 8 _
