From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.iter_linked_list_gen.
Import iter_linked_list.

Import SAWCorePrelude.


Lemma appendList_Nil_r a l : appendList a l List.nil = l.
Proof.
  induction l; eauto.
  simpl; f_equal; eauto.
Qed.

Hint Rewrite appendList_Nil_r : refinesM.


Lemma no_errors_is_elem :
  refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun _ _ => noErrorsSpec).
  unfold noErrorsSpec.
  prove_refinement.
Qed.

Definition is_elem_pure (x:bitvector 64) (l:list (bitvector 64))
  : bitvector 64 :=
  list_rect (fun _ => bitvector 64)
            (intToBv 64 0)
            (fun y l' rec => if bvEq 64 y x then intToBv 64 1 else rec) l.

Lemma is_elem_pure_ref :
  refinesFun is_elem (fun x l => returnM (is_elem_pure x l)).
Proof.
  unfold is_elem, is_elem__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun x l => returnM (is_elem_pure x l)).
  unfold is_elem_pure.
  prove_refinement.
  rewrite appendList_Nil_r; reflexivity.
Qed.

Definition is_elem_spec (x:bitvector 64) (l:list (bitvector 64))
  : CompM (bitvector 64) :=
  orM (assertM (List.In x l) >> returnM (intToBv 64 1))
      (assertM (~ List.In x l) >> returnM (intToBv 64 0)).

Lemma is_elem_spec_ref : refinesFun is_elem is_elem_spec.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_spec.
  prove_refinement_match_letRecM_l.
  - exact is_elem_spec.
  unfold is_elem_spec.
  prove_refinement.
  (* The a0 = [] case. *)
  - continue_prove_refinement_right.
    easy.
  (* The a0 = (s1 :: a1) case where a = s1. *)
  - continue_prove_refinement_left.
    left; easy.
  (* The a0 = (s1 :: a1) case where a <> s1, and we inductively assume
     the left assertion of our specification (in the letRec) *)
  - continue_prove_refinement_left.
    rewrite appendList_Nil_r in e_assert.
    right; easy.
  (* The a0 = (s1 :: a1) case where a <> s1, and we inductively assume
     the right assertion of our specification (in the letRec) *)
  - continue_prove_refinement_right.
    rewrite appendList_Nil_r in e_assert.
    intros []; easy.
  (* The a0 = (s1 :: a1) case where a <> s1, and we inductively assume
     the left assertion of our specification (out of the letRec) *)
  - continue_prove_refinement_left.
    rewrite appendList_Nil_r in e_assert; easy.
  (* The a0 = (s1 :: a1) case where a <> s1, and we inductively assume
     the right assertion of our specification (out of the letRec) *)
  - continue_prove_refinement_right.
    rewrite appendList_Nil_r in e_assert; easy.
Qed.


Definition incr_list_invar :=
  @list_rect (bitvector 64) (fun _ => Prop) True
             (fun x _ rec => isBvslt 64 x (bvsmax 64) /\ rec).

Arguments incr_list_invar !l.

Lemma no_errors_incr_list :
  refinesFun incr_list (fun l => assumingM (incr_list_invar l) noErrorsSpec).
Proof.
  unfold incr_list, incr_list__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun _ l => assumingM (incr_list_invar l) noErrorsSpec).
  unfold noErrorsSpec, BVVec, bitvector in * |- *.
  time "no_errors_incr_list" prove_refinement.
  all: try destruct e_assuming as [?e_assuming ?e_assuming];
       try destruct e_assuming0 as [?e_assuming ?e_assuming];
       try destruct e_assuming1 as [?e_assuming ?e_assuming]; cbn - [bvsmax] in *.
  (* All but one of the remaining goals are taken care of by assumptions we have in scope: *)
  all: try rewrite appendList_Nil_r; try split; eauto.
  (* We just have to show this case is impossible by virtue of our loop invariant: *)
  apply isBvslt_suc_r in e_assuming0.
  rewrite <- e_assuming0, e_if in e_if0.
  apply isBvslt_antirefl in e_if0; contradiction.
Qed.
