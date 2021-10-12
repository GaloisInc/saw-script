From Coq          Require Import Program.Basics.
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Import SAWCorePrelude.

Load "sha512_gen.v".
Import SHA512.

Import VectorNotations.


Definition simpl0_invar (num0 idx num : bitvector 64) :=
  isBvule 64 idx num0 /\ num = bvSub 64 num0 idx.

Lemma no_errors_simpl0 : refinesFun simpl0 (fun num arr => noErrorsSpec).
Proof.
  unfold simpl0, simpl0__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun num0 idx num sum arr _ _ _ => assumingM (simpl0_invar num0 idx num) noErrorsSpec).
  unfold noErrorsSpec, simpl0_invar.
  time "no_errors_simpl0" prove_refinement.
  all: try assumption.
  - assert (isBvult 64 a2 a1).
    + apply isBvule_to_isBvult_or_eq in e_assuming.
      destruct e_assuming; [assumption |].
      apply bvEq_bvSub_r in H.
      symmetry in H; contradiction.
    + rewrite H in e_maybe; discriminate e_maybe.
  - apply isBvult_to_isBvule_suc; assumption.
  - repeat rewrite bvSub_eq_bvAdd_neg.
    rewrite bvAdd_assoc; f_equal.
    rewrite bvNeg_bvAdd_distrib; reflexivity.
  - apply isBvule_zero_n.
  - symmetry; apply bvSub_n_zero.
Qed.


Definition simpl0_spec num : BVVec 64 num (bitvector 8) -> bitvector 64 :=
  foldr _ _ _ (fun a b => bvAdd 64 b (bvUExt 56 8 a)) (intToBv 64 0).

Definition simpl0_letRec_spec num0 idx num (sum : bitvector 64) arr (_ _ _ : unit) :=
  forallM (fun (pf : isBvule 64 idx num0) =>
  assumingM (num = bvSub 64 num0 idx)
            (returnM (arr, bvAdd 64 sum (simpl0_spec (bvSub 64 num0 idx)
                                                     (dropBVVec _ _ _ idx pf arr))))).

Lemma simpl0_spec_ref :
  refinesFun simpl0 (fun num arr => returnM (arr, simpl0_spec num arr)).
Proof.
  unfold simpl0, simpl0__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact simpl0_letRec_spec.
  unfold noErrorsSpec, simpl0_letRec_spec, simpl0_spec.
  time "simpl0_spec_ref" prove_refinement.
  (* Why didn't prove_refinement do this? *)
  3: prove_refinement_eauto; [| apply refinesM_returnM ].
  7: prove_refinement_eauto; [| apply refinesM_returnM ].
  (* same as no_errors_simpl0 *)
  - assert (isBvult 64 a2 a1).
    + apply isBvule_to_isBvult_or_eq in e_forall.
      destruct e_forall; [assumption |].
      apply bvEq_bvSub_r in H.
      symmetry in H; contradiction.
    + rewrite H in e_maybe; discriminate e_maybe.
  - apply isBvult_to_isBvule_suc; assumption.
  - repeat rewrite bvSub_eq_bvAdd_neg.
    rewrite bvAdd_assoc; f_equal.
    rewrite bvNeg_bvAdd_distrib; reflexivity.
  (* unique to this proof *)
  - admit.
  - repeat f_equal.
    admit.
  (* same as no_errors_simpl0 *)
  - apply isBvule_zero_n.
  - symmetry; apply bvSub_n_zero.
  (* unique to this proof *)
  - rewrite bvAdd_id_l.
    repeat f_equal.
    admit.
Admitted.
