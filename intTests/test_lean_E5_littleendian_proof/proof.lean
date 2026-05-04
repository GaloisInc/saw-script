/-
Stress-test E5 (tier 3): littleendian round-trip.

Source: otherTests/saw-core-lean/test_offline_lean_stress.E5_prove0.lean
Cryptol property:
    let littleendian b         = join (reverse b)
        littleendian_inverse b = reverse (split b)
    in \(b : [4][8]) -> littleendian_inverse (littleendian b) == b

Emitted goal is a ~30-line nested gen/atWithDefault/div/mod chain.
The identity holds because join is a left inverse of split (for
exact-multiple widths 32 = 4*8), and reverse is self-inverse.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

theorem goal_closed : goal := by
  intro b
  -- First step: try the simple simp[gen_atWithDefault, bvEq_refl]
  -- sweep. If it doesn't close, diagnose what's left.
  simp [gen_atWithDefault]
  sorry
