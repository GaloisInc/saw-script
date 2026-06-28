import Emitted
import CryptolToLean.SAWCorePrelude_proofs
import CryptolToLean.SAWCoreBitvectors_proofs

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePreludeProofs
open CryptolToLean.SAWCoreBitvectorsProofs

theorem streamFibs_at_zero :
    StreamFibs.streamFibs (Pure.pure (bvNat 8 0)) =
      Pure.pure (bvNat 32 0) := by
  simp [StreamFibs.streamFibs, StreamFibs.fibsPair, StreamFibs.bodyA,
    StreamFibs.bodyB,
    mkStreamFixPairChecked, mkStreamFixPair, mkStreamFixPairIdxA,
    mkStreamFixPairPrefix, streamIdx, atWithDefault, bvToNat_bvNat,
    Pure.pure, Bind.bind, Except.pure, Except.bind]

theorem streamFibs_at_one :
    StreamFibs.streamFibs (Pure.pure (bvNat 8 1)) =
      Pure.pure (bvNat 32 1) := by
  simp [StreamFibs.streamFibs, StreamFibs.fibsPair, StreamFibs.bodyA,
    StreamFibs.bodyB,
    mkStreamFixPairChecked, mkStreamFixPair, mkStreamFixPairIdxA,
    mkStreamFixPairPrefix, streamIdx, atWithDefault, bvToNat_bvNat,
    Pure.pure, Bind.bind, Except.pure, Except.bind]

theorem streamFibs_at_two :
    StreamFibs.streamFibs (Pure.pure (bvNat 8 2)) =
      Pure.pure (bvNat 32 1) := by
  simp [StreamFibs.streamFibs, StreamFibs.fibsPair, StreamFibs.bodyA,
    StreamFibs.bodyB, mkStreamFixPairChecked, mkStreamFixPair,
    mkStreamFixPairIdxA, mkStreamFixPairPrefix,
    streamIdx, atWithDefault, bvToNat_bvNat, Pure.pure, Bind.bind,
    Except.pure, Except.bind]
  show bvAdd 32 (bvNat 32 0) (bvNat 32 1) = bvNat 32 1
  unfold bvAdd bvNat
  rw [vecToBitVec_bitVecToVec, vecToBitVec_bitVecToVec]
  rfl
