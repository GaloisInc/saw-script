/-
t6: two-element sequence equals reverse of the swapped pair over [2][8].

Source: drivers/offline_lean/test_offline_lean.t6_prove0.lean
Cryptol property: \(x : [8]) (y : [8]) -> [x, y] == reverse [y, x]

Current proof-carrying emission: the reverse indexing goes through
`genWithBoundsM` / `atWithProof_checkedM` with derived `subNat 1 i`
indices; the completed outline discharges the derived bounds evidence
with `omega` after normalizing the numeral macros and `subNat`.

Discharge: unfold the checked helpers (including `vecSequenceM` and the
size-2 `Vector.ofFnM` steps); `1 - i` at size 2 collapses the reverse;
each fold element becomes `bvEq` of identical components via `bvEq_refl`,
and simp closes the size-2 all-trues fold.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs
open CryptolToLean.SAWCorePreludeProofs

theorem goal_closed : goal := by
  intro x y
  simp [genWithBoundsM, atWithProof_checkedM, foldrM, subNat, vecSequenceM,
    Vector.ofFnM_succ, Vector.ofFnM_zero,
    CryptolToLean.SAWCorePreludeExtra.iteM, bvEq_refl,
    Pure.pure, Bind.bind, Except.pure, Except.bind]
