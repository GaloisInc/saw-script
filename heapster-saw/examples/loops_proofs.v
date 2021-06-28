From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.loops.
Import loops.

Import SAWCorePrelude.


Lemma no_errors_add_loop : refinesFun add_loop (fun _ _ => noErrorsSpec).
Proof.
  unfold add_loop, add_loop__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun _ _ _ _ => noErrorsSpec).
  unfold noErrorsSpec.
  time "no_errors_add_loop" prove_refinement.
Qed.


Definition add_loop_spec (x y : {_ : bitvector 64 & unit}) : CompM {_ : bitvector 64 & unit}
  := returnM (existT _ (bvAdd 64 (projT1 x) (projT1 y)) tt).

Lemma add_loop_spec_ref : refinesFun add_loop add_loop_spec.
Proof.
  unfold add_loop, add_loop__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun _ _ ret i => add_loop_spec ret i).
  unfold add_loop_spec.
  time "add_loop_spec_ref" prove_refinement.
  - f_equal.
    rewrite bvAdd_assoc.
    rewrite (bvAdd_comm _ a4).
    rewrite <- (bvAdd_assoc _ _ _ a4).
    compute_bv_funs.
    rewrite bvAdd_id_l.
    reflexivity.
  - rewrite isBvule_n_zero in e_if.
    rewrite e_if, bvAdd_id_r.
    reflexivity.
Qed.


(* Add `add_loop_spec_ref` to the hint database. Unfortunately, Coq will not unfold refinesFun
   and add_loop_spec when rewriting, and the only workaround I know right now is this :/ *)
Definition add_loop_spec_ref' : ltac:(let tp := type of add_loop_spec_ref in
                                      let tp' := eval unfold refinesFun, add_loop_spec in tp
                                       in exact tp') := add_loop_spec_ref.
Hint Rewrite add_loop_spec_ref' : refinement_proofs.

Lemma no_errors_sign_of_sum : refinesFun sign_of_sum (fun _ _ => noErrorsSpec).
Proof.
  unfold sign_of_sum, sign_of_sum__tuple_fun, noErrorsSpec.
  time "no_errors_sign_of_sum" prove_refinement.
Qed.

Definition sign_of_sum_spec (x y : {_ : bitvector 64 & unit}) : CompM {_ : bitvector 64 & unit} :=
  orM (     assertM (isBvslt _ (intToBv _ 0) (bvAdd _ (projT1 x) (projT1 y)))
                    >> returnM (existT _ (intToBv _ 1) tt))
      (orM (assertM (isBvslt _ (bvAdd _ (projT1 x) (projT1 y)) (intToBv _ 0))
                    >> returnM (existT _ (intToBv _ (-1)) tt))
           (assertM (bvAdd _ (projT1 x) (projT1 y) = intToBv _ 0)
                    >> returnM (existT _ (intToBv _ 0) tt))).

Lemma sign_of_sum_spec_ref : refinesFun sign_of_sum sign_of_sum_spec.
Proof.
  unfold sign_of_sum, sign_of_sum__tuple_fun, sign_of_sum_spec.
  time "sign_of_sum_spec_ref" prove_refinement.
  - continue_prove_refinement_left.
    assumption.
  - continue_prove_refinement_right;
    continue_prove_refinement_left.
    assumption.
  - continue_prove_refinement_right;
    continue_prove_refinement_right.
    apply isBvsle_antisymm; assumption.
Qed.


(* Add `no_errors_sign_of_sum` to the hint database. Unfortunately, Coq will not unfold refinesFun
   and no_errors_sign_of_sum when rewriting, and the only workaround I know right now is this :/ *)
Definition no_errors_sign_of_sum' : ltac:(let tp := type of no_errors_sign_of_sum in
                                          let tp' := eval unfold refinesFun, noErrorsSpec in tp
                                           in exact tp') := no_errors_sign_of_sum.
Hint Rewrite no_errors_sign_of_sum' : refinement_proofs.

Lemma no_errors_compare_sum : refinesFun compare_sum (fun _ _ _ => noErrorsSpec).
Proof.
  unfold compare_sum, compare_sum__tuple_fun, noErrorsSpec.
  time "no_errors_compare_sum" prove_refinement.
Qed.


(* Remove `no_errors_sign_of_sum` from the database! *)
Remove Hints no_errors_sign_of_sum' : refinement_proofs.

(* Add `sign_of_sum_spec_ref` to the hint database. Unfortunately, Coq will not unfold refinesFun
   and no_errors_sign_of_sum when rewriting, and the only workaround I know right now is this :/ *)
Definition sign_of_sum_spec_ref' : ltac:(let tp := type of sign_of_sum_spec_ref in
                                         let tp' := eval unfold refinesFun, sign_of_sum_spec in tp
                                          in exact tp') := sign_of_sum_spec_ref.
Hint Rewrite sign_of_sum_spec_ref' : refinement_proofs.


Definition compare_sum_spec (x y z : {_ : bitvector 64 & unit}) : CompM {_ : bitvector 64 & unit} :=
  orM (     assertM (isBvslt _ (projT1 x) (bvAdd _ (projT1 y) (projT1 z)))
                    >> returnM (existT _ (intToBv _ 1) tt))
      (orM (assertM (isBvslt _ (bvAdd _ (projT1 y) (projT1 z)) (projT1 x))
                    >> returnM (existT _ (intToBv _ (-1)) tt))
           (assertM (projT1 x = bvAdd _ (projT1 y) (projT1 z))
                    >> returnM (existT _ (intToBv _ 0) tt))).

Lemma compare_sum_spec_ref : refinesFun compare_sum compare_sum_spec.
Proof.
  unfold compare_sum, compare_sum__tuple_fun, compare_sum_spec.
  time "compare_sum_spec_ref" prove_refinement.
  all: rewrite bvSub_zero_bvNeg in e_assert.
  (* Note that there are two versions of each case because of the if! *)
  (* The `x < y + z` case: *)
  1,4: continue_prove_refinement_left.
  1,2: rewrite bvslt_bvSub_r, bvSub_eq_bvAdd_neg, bvAdd_comm.
  1,2: assumption.
  (* The `x > y + z` case: *)
  1,3: continue_prove_refinement_right;
       continue_prove_refinement_left.
  1,2: rewrite bvslt_bvSub_l, bvSub_eq_bvAdd_neg, bvAdd_comm.
  1,2: assumption.
  (* The `x = y + z` case: *)
  1,2: continue_prove_refinement_right;
       continue_prove_refinement_right.
  1,2: rewrite bvEq_bvSub_r, bvSub_eq_bvAdd_neg, bvAdd_comm.
  1,2: symmetry; assumption.
Qed.
