From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.iter_linked_list.
Import iter_linked_list.

Import SAWCorePrelude.


Lemma appendList_Nil_r a l : appendList a l List.nil = l.
Proof.
  induction l; eauto.
  simpl; f_equal; eauto.
Qed.


Definition incr_list_invar :=
  @list_rect {_ : bitvector 64 & unit} (fun _ => Prop) True
           (fun x _ rec => isBvult 64 (projT1 x) (intToBv 64 0x7fffffffffffffff) /\ rec).

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
       try destruct e_assuming1 as [?e_assuming ?e_assuming]; simpl in *.
  (* All but one of the remaining goals are taken care of by assumptions we have in scope: *)
  all: try (split; [| rewrite appendList_Nil_r]); eauto.
  (* We just have to show this case is impossible by virtue of our loop invariant: *)
  apply isBvult_to_isBvule_suc in e_assuming0.
  apply bvule_msb_l in e_assuming0; try assumption.
  compute_bv_funs in e_assuming0; inversion e_assuming0.
Qed.
