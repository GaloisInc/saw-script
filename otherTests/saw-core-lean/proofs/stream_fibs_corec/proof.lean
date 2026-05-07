/-
H-2: end-to-end semantic discharge for the PairStreamCorec lowering
on `StreamFibs.cry`.

The Cryptol program

  fibs0 = [0] # fibs1
  fibs1 = [1] # [a + b | a <- fibs0 | b <- fibs1]
  streamFibs x = fibs0 @ x

lowers (Phase 5 PairStreamCorec recognizer) to a SAWCore
`fix (PairType1 (Stream Vec32) (Stream Vec32)) ...`, which the
recognizer matches and the lowering emits as a `mkStreamFixPair`
call followed by `pairFst` + `streamIdx`.

Companion to `recursion_stream_corec` (which exercises the
single-stream `mkStreamFix` lowering on `RecOnes.cry`); this is
the second of the two end-to-end recursion-discharge proofs that
the Phase 5b L-discipline-2 exit criterion mandated. Pin H-2 from
2026-05-06_pre-merge-audit.md.

Concrete values (computed from the Cryptol program by hand):
  streamFibs 0 = 0
  streamFibs 1 = 1
  streamFibs 2 = 1   ← uses bvAdd through the cross-stream lookup

Discharge strategy: unfold the lowering layer (`mkStreamFixPair`,
`mkStreamFixPairIdxA`, `mkStreamFixPairPrefix`); both `Stream` and
`PairType` are single-constructor inductives, so the
`@Stream.rec` / `@PairType.rec` wrapping the emission introduces
iota-reduces under `rfl`. The structural-prefix builder unfolds
recursively up through the requested index. At small concrete
indices the body bottoms out in `bvNat` / `bvAdd` on literal byte
values; mathlib's `BitVec.ofNat` + `+` reduce under `decide` /
`rfl` once we pin the index via `bvToNat_bvNat`.

If the lowering broke — e.g., dropped the lookup substitution,
swapped `mkStreamFixPairIdxA` ↔ `IdxB`, swapped `bodyα` ↔ `bodyβ`
at emission, or mis-emitted the seed-vec — these proofs fail. The
textual `.module.lean.good` diff cannot detect any of those (it
only pins the emission shape, not the semantics).
-/

import Emitted
import CryptolToLean
import CryptolToLean.SAWCorePrelude_proofs
import CryptolToLean.SAWCoreBitvectors_proofs

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePreludeProofs
open CryptolToLean.SAWCoreBitvectorsProofs

/-- streamFibs at index 0 — fibs0[0] = 0. The seed value of the
left-stream `[0] # fibs1`; exercises only the base case of
`mkStreamFixPairPrefix`. The `bodyα` / `bodyβ` accesses to lkα /
lkβ never fire (the seed-vec at index 0 returns the explicit
literal). -/
theorem streamFibs_at_zero :
    StreamFibs.streamFibs (bvNat 8 0) = bvNat 32 0 := by
  unfold StreamFibs.streamFibs
  rw [bvToNat_bvNat 8 0 (by decide)]
  unfold mkStreamFixPair mkStreamFixPairIdxA mkStreamFixPairPrefix
  unfold atWithDefault
  rfl

/-- streamFibs at index 1 — fibs0[1] = fibs1[0] = 1. Exercises
the cross-stream lookup: `bodyα` reads `lkβ` at `i-1`, and at
i=1 that lkβ lookup falls into the prefix's freshly-built fibs1[0]
slot. If the recognizer mis-attached `lkα` vs `lkβ` to bodyα,
this is the smallest case that catches it. -/
theorem streamFibs_at_one :
    StreamFibs.streamFibs (bvNat 8 1) = bvNat 32 1 := by
  unfold StreamFibs.streamFibs
  rw [bvToNat_bvNat 8 1 (by decide)]
  unfold mkStreamFixPair mkStreamFixPairIdxA mkStreamFixPairPrefix
  unfold atWithDefault
  rfl

/-- streamFibs at index 2 — fibs0[2] = fibs1[1] = fibs0[0] + fibs1[0]
= 0 + 1 = 1. The first index where the *β-side* body actually fires
its recursive `lkα + lkβ` step (rather than reading the literal
seed `[1]`); the result then propagates back into the α-side at
i=2. If the translator dropped or mis-substituted either lookup
function, this is the smallest case that catches it.

Note that this also exercises `bvAdd 32 (bvNat 32 0) (bvNat 32 1)`,
so it pins that the `+` in the Cryptol comprehension routes through
the BitVec-backed `bvAdd` (i.e. doesn't get folded away or replaced
with Nat addition). -/
theorem streamFibs_at_two :
    StreamFibs.streamFibs (bvNat 8 2) = bvNat 32 1 := by
  unfold StreamFibs.streamFibs
  rw [bvToNat_bvNat 8 2 (by decide)]
  unfold mkStreamFixPair mkStreamFixPairIdxA mkStreamFixPairPrefix
  unfold atWithDefault
  -- The β-side body produces `bvAdd 32 (bvNat 32 0) (bvNat 32 1)`
  -- as the fibs1[1] entry; reduce that via the BitVec round-trip.
  show bvAdd 32 (bvNat 32 0) (bvNat 32 1) = bvNat 32 1
  unfold bvAdd bvNat
  rw [vecToBitVec_bitVecToVec, vecToBitVec_bitVecToVec]
  rfl
