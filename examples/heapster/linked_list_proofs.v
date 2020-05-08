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

Definition noErrorsSpec {A} : CompM A := existsM (fun a => returnM a).

Import SAWCorePrelude.


Lemma no_errors_is_elem : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun, noErrorsSpec.
  apply refinesFun_multiFixM_fst. simpl. intros x l.
  rewrite simpl_letRecM0.
  apply refinesM_either; intros.
  - eapply refinesM_existsM_r. reflexivity.
  - apply refinesM_sigT_rect; intros.
    apply refinesM_if; intros.
    + eapply refinesM_existsM_r. reflexivity.
    + rewrite existsM_bindM.
      apply refinesM_existsM_l; intros. rewrite returnM_bindM.
      apply refinesM_sigT_rect; intros.
      eapply refinesM_existsM_r. reflexivity.
Qed.
