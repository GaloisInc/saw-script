/-
Sequence-surgery: genWithProof read over [4][8].

Source: workflows/cryptol_seq_surgery/test_cryptol_seq_surgery.gen_prove0.lean
SAWCore goal: bvEq 8 (at 4 _ (genWithProof 4 _ (\i pf -> v)) 0) v

The obligation exercises `genWithProof_checkedM` (the target checked
helper) composed with `atWithProof_checkedM`.

Completed-outline row: the emitted `def goal` embeds `all_goals sorry`
fallbacks in its bounds tactics. Those fallbacks are vacuous — the
`omega` branch closes the bounds first — so `completed.lean` is the
generated outline with the (never-taken) fallbacks stripped and
`goal_holds` discharged; the harness drift-checks that the stripped
`goal` is definitionally the generated `goal`.

Discharge (in completed.lean): `genWithProof_checkedM` reduces to
`genWithBoundsM = Vector.ofFnM (fun i => pure v)`; the simp lemma
`ofFnM_except_ok` collapses the constant `Except.ok`-valued generator
to `Except.ok (Vector.ofFn (fun _ => v))`. Reading index 0 via
`atWithProof_checkedM` (`Vector.getElem_ofFn`) yields `v`, and
`bvEq 8 v v` closes by `bvEq_refl`.
-/

import Emitted

theorem goal_closed : goal :=
  goal_holds
