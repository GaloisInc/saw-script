/-
Sequence-surgery: sliceWithProof read over [8][8].

Source: workflows/cryptol_seq_surgery/test_cryptol_seq_surgery.slice_prove0.lean
SAWCore goal: bvEq 8 (at 4 _ (sliceWithProof _ 8 2 4 pf xs) 0) (at 8 _ xs 2)

The obligation exercises `sliceWithProof_checkedM` (the target checked
helper) composed with `atWithProof_checkedM`.

Completed-outline row: the emitted `def goal` embeds `all_goals sorry`
fallbacks in its bounds tactics. Those fallbacks are vacuous — the
`omega` branch closes the bounds first — so `completed.lean` is the
generated outline with the (never-taken) fallbacks stripped and
`goal_holds` discharged; the harness drift-checks that the stripped
`goal` is definitionally the generated `goal`.

Discharge (in completed.lean): `sliceWithProof_checkedM` builds
`Vector.ofFn (fun j => vec[off + j.val])` with off = 2; element 0 of
the slice is `vec[2 + 0]`, which `Nat.add_zero` collapses to `vec[2]`,
matching the right-hand `at xs 2 = vec[2]`. `bvEq 8 vec[2] vec[2]`
closes by `bvEq_refl`.
-/

import Emitted

theorem goal_closed : goal :=
  goal_holds
