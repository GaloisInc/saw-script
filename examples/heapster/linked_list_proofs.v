From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From Records      Require Import Records.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Load "linked_list.v".
Import linked_list.

Import SAWCorePrelude.


Lemma no_errors_is_elem : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  prove_refinesFun.
Qed.

Lemma no_errors_is_elem_manual : refinesFun is_elem (fun _ _ => noErrorsSpec).a
Proof.
  unfold noErrorsSpec.
  apply refinesFun_multiFixM_fst. intros x l.
  apply refinesM_letRecM0.
  apply refinesM_either_l; intros.
  - eapply refinesM_existsM_r. reflexivity.
  - apply refinesM_sigT_rect_l; intros.
    apply refinesM_if_l; intros.
    + eapply refinesM_existsM_r. reflexivity.
    + rewrite existsM_bindM.
      apply refinesM_existsM_l; intros. rewrite returnM_bindM.
      apply refinesM_sigT_rect_l; intros.
      eapply refinesM_existsM_r. reflexivity.
Qed.
