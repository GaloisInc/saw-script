/-
Proof gap: ChaCha20 round-folding companion proof.

This file is preserved as a stress proof attempt, not an accepted backend proof
regression. The proof is axiom-clean in intent, but it currently exceeds the
practical elaboration/heartbeat budget under the default harness. It should
move back to `proofs/` only after the generated terms or proof script are
factored enough to check reliably without heartbeat inflation.

Target property: `iround 0 r == r`.

`iround : [64] -> Round -> Round` from
`deps/cryptol-specs/.../chacha20.cry` is defined as
`iround n r = (iterate once r) @ n` where `once` increments
the counter (state[12]). At `n = 0`, the seed semantics of
iterate dictates the result is `r` itself — non-trivially:
the proof must actually *reduce* `cryptolIterate once r @ 0`
to `r`, which exercises `cryptolIterate.cryptolIterateIdx` at
the base case (vs the reflexive `core x == core x` proof in
`cryptol_chacha20_core_iterate`, which closes by `bvEq_refl`
without ever reducing the iterate).

Discharge plan:
  * `foldr_and_gen_eq_true_of_all 16` — reduces the per-byte
    equality to `∀ i < 16, byte_i = true`.
  * Simp `bvToNat (bvNat 64 0) = 0` so the Stream.rec fires at
    a concrete index.
  * Unfold `cryptolIterate` so `Stream.rec` iota-reduces to the
    `cryptolIterateIdx` lambda body, and at index 0 returns the
    seed `r`.
  * The remaining per-position `bvEq 32 r[i] r[i] = true`
    closes via `bvEq_refl`.
-/

import Emitted

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs
open CryptolToLean.SAWCorePreludeExtra

theorem goal_closed : goal := by
  intro r
  apply foldr_and_gen_eq_true_of_all 16
  intro i hi
  -- The per-byte equality is `bvEq 32 (atWithDefault 16 _ (Stream.rec
  -- ... (cryptolIterate ... once r)) i) (atWithDefault 16 _ r i)`.
  -- Reduce the bvToNat-of-literal index, then unfold cryptolIterate so
  -- Stream.rec iota-fires to the cryptolIterateIdx base case (= seed r).
  rw [bvToNat_bvNat 64 0 (by decide)]
  unfold cryptolIterate
  -- Now Stream.rec on MkStream reduces to the case-arm applied to the
  -- inner Nat → Vec 16 ... lambda; at index 0 that lambda returns r
  -- via the cryptolIterateIdx zero case.
  show bvEq 32
        (atWithDefault 16 (Vec 32 Bool) _ (cryptolIterate.cryptolIterateIdx _ _ r 0) i)
        (atWithDefault 16 (Vec 32 Bool) _ r i) = true
  unfold cryptolIterate.cryptolIterateIdx
  exact bvEq_refl 32 _
