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
  unfold is_elem, is_elem__tuple_fun, noErrorsSpec.
  prove_refinement.
Qed.

Lemma no_errors_is_elem_manual : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold noErrorsSpec.
  apply refinesFun_multiFixM_fst. intros x l.
  apply refinesM_letRecM0.
  apply refinesM_either_l; intros.
  - eapply refinesM_existsM_r. reflexivity.
  - apply refinesM_if_l; intros.
    + eapply refinesM_existsM_r. reflexivity.
    + rewrite existsM_bindM.
      apply refinesM_existsM_l; intros. rewrite returnM_bindM.
      eapply refinesM_existsM_r. reflexivity.
Qed.


(*
Fixpoint is_elem_spec (x:bitvector 64) (l:W64List) : CompM {_:bitvector 64 & unit} :=
  match l with
  | W64Nil => returnM (existT _ (bvNat 64 0) tt)
  | W64Cons y l' =>
    if bvEq 64 y x then returnM (existT _ (bvNat 64 1) tt) else
      is_elem_spec x l'
  end.
*)

Definition is_elem_spec (x:bitvector 64) : W64List -> CompM {_:bitvector 64 & unit} :=
  W64List_rect (fun _ => CompM {_:bitvector 64 & unit})
               (returnM (existT _ (bvNat 64 0) tt))
               (fun y l' rec =>
                  if bvEq 64 y x then returnM (existT _ (bvNat 64 1) tt) else rec).

Arguments is_elem_spec /.

Lemma bvEq_sym n x y : bvEq n x y = bvEq n y x.
  admit.
Admitted.

From Coq Require Import Nat.

Lemma bvEq_eqb n x y : bvEq n (bvNat n x) (bvNat n y) = eqb x y.
  admit.
Admitted.

Definition bindM_returnM_CompM A (m:CompM A) : m >>= (fun x => returnM x) ~= m :=
  bindM_returnM (M:=CompM) A m.

Lemma is_elem_correct : refinesFun is_elem is_elem_spec.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_spec.
  prove_refinement.
Qed.
