/-
Tuple-projection coverage proof. Audit (2026-05-06): drivers/tuples/
only emit-diff'd, no end-to-end discharge. This pins the Cryptol
property `\(x y : [8]) -> ((x, y).0 : [8]) == x` through Lean.

Cryptol's `(x, y)` translates to `PairType.PairValue` and `.0`
translates to `Pair_fst`. After `Pair_fst` reduces (it pattern-
matches on the constructor), the goal becomes `bvEq 8 x x = true`,
which is `bvEq_refl`.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

theorem goal_closed : goal := by
  intro x y
  -- Pair_fst on a PairValue reduces by definition.
  show bvEq 8 x x = Bool.true
  exact bvEq_refl 8 x
