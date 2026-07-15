/-
Sequence-surgery: updWithProof round-trip over [4][8].

Source: workflows/cryptol_seq_surgery/test_cryptol_seq_surgery.upd_prove0.lean
SAWCore goal: bvEq 8 (at 4 _ (updWithProof 4 _ xs 1 v pf) 1) v

The obligation exercises `updWithProof_checkedM` (the target checked
helper) composed with `atWithProof_checkedM`.

Completed-outline row: the emitted `def goal` embeds `all_goals sorry`
fallbacks in its bounds tactics. Those fallbacks are vacuous — the
`omega` branch closes `1 < 4` first — so `completed.lean` is the
generated outline with the (never-taken) fallbacks stripped and
`goal_holds` discharged; the harness drift-checks that the stripped
`goal` is definitionally the generated `goal`.

Discharge (in completed.lean): `updWithProof_checkedM` builds
`Vector.ofFn (fun j => if j.val = 1 then v else vec[j])`; reading index
1 via `atWithProof_checkedM` selects the `j = 1` branch
(`Vector.getElem_ofFn` + `dite_true`), yielding `v`. `bvEq 8 v v`
closes by `bvEq_refl`; the `Except.ok` wrappers match.
-/

import Emitted

theorem goal_closed : goal :=
  goal_holds
