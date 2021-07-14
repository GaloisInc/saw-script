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

Require Import Examples.arrays.
Import arrays.

Import VectorNotations.

Definition bvMem_lo := intToBv 64 0xf000000000000000.
Definition bvMem_hi := intToBv 64 0x0fffffffffffffff.


Definition zero_array_precond x
  := isBvsle 64 (intToBv 64 0) x /\ isBvsle 64 x bvMem_hi.

Definition zero_array_invariant x x' (i : { _ & unit })
  := isBvsle 64 (intToBv 64 0) (projT1 i) /\ isBvsle 64 (projT1 i) x /\ x = x'.

Lemma no_errors_zero_array
  : refinesFun zero_array (fun x _ => assumingM (zero_array_precond x) noErrorsSpec).
Proof.
  unfold zero_array, zero_array__tuple_fun, zero_array_precond.
  prove_refinement_match_letRecM_l.
  - exact (fun a' _ i => assumingM (zero_array_invariant a a' i) noErrorsSpec).
  unfold zero_array_invariant, noErrorsSpec.
  fold bvMem_lo; fold bvMem_hi.
  time "no_errors_zero_array" prove_refinement.
  (* A number of the remaining cases are covered exactly by hypotheses we already have in
     scope (e.g. proving the loop invariant holds initially). Note that `prove_refinement`
     doesn't do this automatically because it may matter which hypothesis is used, if
     there are multiple. For this poof though, it doesn't. *)
  all: try assumption.
  (* Proving that the loop invariant holds inductively: *)
  - transitivity a3.
    + assumption.
    + apply isBvsle_suc_r.
      rewrite e_assuming2, e_assuming0.
      reflexivity.
  - apply isBvslt_to_isBvsle_suc.
    apply isBvult_to_isBvslt_pos; assumption.
  (* Proving that these branches are impossible, by virtue of our loop invariant: *)
  - rewrite <- e_assuming1 in e_if0.
    discriminate e_if0.
  - rewrite e_assuming2, e_assuming0 in e_if0.
    apply isBvslt_antirefl in e_if0; contradiction e_if0.
  (* The remaining cases are all taken care of by either prove_refinement or assumption! *)
Qed.


Definition contains0_precond l
  := isBvsle 64 (intToBv 64 0) l /\ isBvsle 64 l bvMem_hi.

Definition contains0_invariant l l' (i : { _ & unit })
  := isBvsle 64 (intToBv 64 0) (projT1 i) /\ isBvsle 64 (projT1 i) l /\ l = l'.

(* This proof is *identical* to no_errors_zero_array except for in the one noted spot *)
Lemma no_errors_contains0
  : refinesFun contains0 (fun x _ => assumingM (contains0_precond x) noErrorsSpec).
Proof.
  unfold contains0, contains0__tuple_fun, contains0_precond.
  prove_refinement_match_letRecM_l.
  - exact (fun a' _ i => assumingM (contains0_invariant a a' i) noErrorsSpec).
  unfold contains0_invariant, noErrorsSpec.
  fold bvMem_lo; fold bvMem_hi.
  time "no_errors_contains0" prove_refinement.
  all: try assumption.
  (* Different from no_errors_zero_array - this used to be taken care of by `prove_refinement`!
     (FIXME Figure out why this fails to be automated here but not above.) *)
  - rewrite e_if in e_maybe.
    discriminate e_maybe.
  - transitivity a3.
    + assumption.
    + apply isBvsle_suc_r.
      rewrite e_assuming2, e_assuming0.
      reflexivity.
  - apply isBvslt_to_isBvsle_suc.
    apply isBvult_to_isBvslt_pos; assumption.
  - rewrite <- e_assuming1 in e_if0.
    discriminate e_if0.
  - rewrite e_assuming2, e_assuming0 in e_if0.
    apply isBvslt_antirefl in e_if0; contradiction e_if0.
Qed.


Definition sum_2d_precond l1 l2
  := isBvsle 64 (intToBv 64 0) l1 /\ isBvsle 64 l1 bvMem_hi /\
     isBvsle 64 (intToBv 64 0) l2 /\ isBvsle 64 l2 bvMem_hi.

Definition sum_2d_invariant1 (l1 l1' l2 l2' : bitvector 64) (i j : { _ & unit })
  := isBvsle 64 (intToBv 64 0) (projT1 i) /\ isBvslt 64 (projT1 i) l1 /\ l1 = l1' /\
     isBvsle 64 (intToBv 64 0) (projT1 j) /\ isBvsle 64 (projT1 j) l2 /\ l2 = l2'.

Definition sum_2d_invariant2 (l1 l1' l2 l2' : bitvector 64) (i : { _ & unit })
  := isBvsle 64 (intToBv 64 0) (projT1 i) /\ isBvsle 64 (projT1 i) l1 /\ l1 = l1' /\ l2 = l2'.

Lemma no_errors_sum_2d
  : refinesFun sum_2d (fun l1 l2 _ => assumingM (sum_2d_precond l1 l2) noErrorsSpec).
Proof.
  unfold sum_2d, sum_2d__tuple_fun, sum_2d_precond.
  time "no_errors_sum_2d (1/2)" prove_refinement_match_letRecM_l.
  - exact (fun a' a0' _ _ i j => assumingM (sum_2d_invariant1 a a' a0 a0' i j) noErrorsSpec).
  - exact (fun a' a0' _ _ i => assumingM (sum_2d_invariant2 a a' a0 a0' i) noErrorsSpec).
  unfold sum_2d_invariant1, sum_2d_invariant2, noErrorsSpec.
  fold bvMem_lo; fold bvMem_hi.
  time "no_errors_sum_2d (2/2)" prove_refinement.
  all: try assumption.
  * rewrite <- isBvult_to_isBvslt_pos in e_assuming4; try assumption.
    rewrite e_assuming4 in e_maybe.
    discriminate e_maybe.
  * rewrite <- isBvsle_suc_r; try assumption.
    rewrite e_assuming6, e_assuming2.
    reflexivity.
  * apply isBvslt_to_isBvsle_suc, isBvult_to_isBvslt_pos; assumption.
  * rewrite <- e_assuming5 in e_if2.
    vm_compute in e_if2; inversion e_if2.
  * rewrite e_assuming6, e_assuming2 in e_if2.
    apply isBvslt_antirefl in e_if2; inversion e_if2.
  * rewrite <- e_assuming3 in e_if0.
    vm_compute in e_if0; inversion e_if0.
  * rewrite e_assuming4, e_assuming0 in e_if0.
    apply isBvslt_antirefl in e_if0; inversion e_if0.
  * rewrite e_assuming3.
    apply isBvsle_suc_r, isBvslt_to_isBvsle.
    rewrite e_assuming4, e_assuming0.
    reflexivity.
  * apply isBvslt_to_isBvsle_suc; assumption.
  * apply isBvult_to_isBvslt_pos; assumption.
Qed.
