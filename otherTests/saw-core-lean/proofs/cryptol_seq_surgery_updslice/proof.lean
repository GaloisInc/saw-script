/-
Sequence-surgery: updSliceWithProof region overwrite over [8][8].

Source: workflows/cryptol_seq_surgery/test_cryptol_seq_surgery.updslice_prove0.lean
SAWCore goal:
  bvEq 8 (at 8 _ (updSliceWithProof _ 8 2 4 pf xs ys) 2) (at 4 _ ys 0)

The obligation exercises `updSliceWithProof_checkedM` (the target
checked helper) composed with `atWithProof_checkedM`.

Completed-outline row: the emitted `def goal` embeds `all_goals sorry`
fallbacks in its bounds tactics. Those fallbacks are vacuous — the
`omega` branch closes the bounds first — so `completed.lean` is the
generated outline with the (never-taken) fallbacks stripped and
`goal_holds` discharged; the harness drift-checks that the stripped
`goal` is definitionally the generated `goal`.

Discharge (in completed.lean): `updSliceWithProof_checkedM` builds a
`Vector.ofFn` whose element j is `ys[j - off]` when `off <= j < off+len`
(off = 2, len = 4) and `xs[j]` otherwise. At j = 2 both region guards
hold — discharged by `dif_pos (… by omega)` — selecting `ys[2 - 2]`,
which `Nat.sub_self` collapses to `ys[0]`, matching `at ys 0`. The
comparison `bvEq 8 ys[0] ys[0]` closes by `bvEq_refl`.
-/

import Emitted

theorem goal_closed : goal :=
  goal_holds
