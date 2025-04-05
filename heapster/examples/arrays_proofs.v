From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From EnTree  Require Import Automation.
Require Import Lia.
From CryptolToCoq Require Import SAWCoreBitvectorsZifyU64.
      
Require Import Examples.common.
Require Import Examples.arrays_gen.
Import arrays.

Import SAWCorePrelude.

Import VectorNotations.

Set Nested Proofs Allowed.
Lemma UIP_bv :
  forall {n} (x y : bitvector n) (p1 p2 : x = y), p1 = p2.
Proof.
  intros.
  apply UIP_dec.
  clear. intros.
  refine (eq_dec _ boolEq _ n x y).
  clear. intros.
  split; intros H.
  - destruct x; destruct y; auto.
  - subst x. destruct y; reflexivity.
Qed.
Require Import Coq.Program.Tactics.

Declare Scope bv_64.
Local Open Scope bv_64.
Bind Scope bv_64 with bitvector.

Infix "+":= (bvAdd 64) (at level 50,  left associativity): bv_64.
Infix "-":= (bvSub 64) (at level 50,  left associativity): bv_64.
Infix "<":= (isBvslt 64) (at level 70): bv_64.
Infix "<=":= (isBvsle 64) (at level 70): bv_64.

(*This is a prototype of a tactic to solve all signed inequalities for
Boolean vectors, as long as there is no overflow. Ideally, if the
tactic fails, it will show you the bounds you need to prove that thre
is no overflow. You probably missed them in your invariants.

The idea is pretty simple: convert everything to to `Int` and, becasue
there is no overflow, we can remove the module quantifiers and crush
it with standard lia.

TO DO:

- Support all arith relations eq[ ], lt[ ], gt[ ], le[✓], ge[ ]

- Don't directly apply rewrites to all subgoals for efficiency

- Recognize when there is a terminal "node" to apply `lia`. Right now
  we attempt lia at every step, whcih is wasteful.

 *)

Lemma eq_bvToInt:
  forall n a b,
    (BinInt.Z.lt (bvToInt n a) (bvToInt n b)) ->
    isBvslt n a b.
Proof.
Admitted.
Lemma lt_bvToInt:
  forall n a b,
    (BinInt.Z.lt (bvToInt n a) (bvToInt n b)) ->
    isBvslt n a b.
Proof.
Admitted.
Lemma le_bvToInt:
  forall n a b,
    (BinInt.Z.le (bvToInt n a) (bvToInt n b)) ->
    isBvsle n a b.
Proof.
Admitted.


Ltac bvToInt_ineq:=
  first [apply eq_bvToInt |
          apply lt_bvToInt |
          apply le_bvToInt].

Ltac remove_mods:=
  (*TODO: Add other operations*)
  try rewrite bvAdd_Zadd_mod_64;
  try rewrite bvSub_Zsub_mod_64;
  try rewrite bvMul_Zmul_mod_64;
  repeat rewrite bvToInt_intToBv_64;
  repeat rewrite BinInt.Z.mod_small.

Ltac solve_bv_no_overflow:=
  try lia;
  match goal with
  | |- isBvsle _ ?LHA ?RHS =>
      apply le_bvToInt
  | |- isBvslt _ ?LHA ?RHS =>
       apply lt_bvToInt
  end; remove_mods;
  try solve_bv_no_overflow.



Definition bvMem_lo := intToBv 64 0xf000000000000000.
Definition bvMem_hi := intToBv 64 0x0fffffffffffffff.


Definition zero_array_precond x
  := isBvsle 64 (intToBv 64 0) x /\ isBvsle 64 x bvMem_hi.

Definition zero_array_invariant x x' i
  := isBvsle 64 (intToBv 64 0) i /\ isBvsle 64 i x /\ x = x'.

Record HeVector T :=
  someVector {
     hvLen1 : nat 
    ; hvLen2 : _
    ; theVector : BVVec hvLen1 hvLen2 T
    }.
Arguments someVector {T hvLen1 hvLen2} theVector.


(* Simpler version of `inversion_sigma` where the inversion is only applied if the hyp has the same *)
Ltac simple_inv_sigma:=
  match goal with
  | H: (_; ?x) = (_; ?y) |- _ => eapply inj_pair2 in H; try subst x
  end.
Ltac inv_with_sigma H:= inversion H; repeat simple_inv_sigma.
Tactic Notation "inv_someVector" "in" "*" := 
  match goal with H: someVector _ = someVector _ |- _ => inv_with_sigma H end.


Lemma HeVectorToSigma:
  forall len len' vec vec',
  (exists (Plen : len = len'),
    eq_rect len (fun x => BVVec 64 x (bitvector 64)) vec len' Plen = vec') ->
  someVector vec = someVector vec'.
Proof. intros * [Plen Heq]. subst len'.
       rewrite <- eq_rect_eq in Heq; subst; auto.
Qed.

Hint Extern 101 (IntroArg ?n (someVector ?a = someVector ?b) _) =>
       let e1 := argName n in IntroArg_intro e1;
(eapply HeVectorToSigma in e1);
revert e1; apply (IntroArg_fold n _ _) : refines prepostcond.

Polymorphic Lemma IntroArg_someVector T n m a1 a2 b1 b2 (eq : a1 = a2) goal :
  IntroArg n (eq_rect _ (fun x => BVVec m x T) b1 _ eq = b2) (fun _ => goal) ->
  IntroArg n (@someVector T m a1 b1 = @someVector T m a2 b2) (fun _ => goal).
Proof.
  destruct eq.
  intros HH a.
  inv_with_sigma a.
  eapply HH; reflexivity.
Qed.

Hint Extern 101 (IntroArg ?n ?A ?g) =>
  simple apply IntroArg_someVector; idtac "Done it"
  : refines prepostcond.

Lemma no_errors_zero_array x y:
  spec_refines_eq (zero_array x y)
    (total_spec (fun '(len, vec, dec) =>  zero_array_precond len) (fun _ _ => True) (x,y, bvAdd _ x (intToBv _ 1))).
Proof.
  intros; unfold_function.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact (bvToNat _ x1).
  - prepost_case 0 0.
    + exact (someVector a = someVector a0 /\
            x = x1 /\
            bvAdd _ x (intToBv _ 1) = x2).
    + exact (someVector r = someVector r0).
    + prepost_case 1 0.
      * exact (someVector a = someVector a0 /\
                 x = x2 /\
                 x3 = bvSub _ x0 x1 /\
                 zero_array_invariant x0 x x1).
      * exact ( (someVector r = someVector r0)).
      * prepost_exclude_remaining.
  - prove_refinement_continue;
      (* Need to add `inv_someVector` to the automation to reduce better*)
      try inv_someVector in *.
    (* with NoRewrite NoSolve *)
    + reflexivity.
    + assert (HH: isBvule _ x0 (bvsmax _)).
      { clear - e_assume.
        destruct e_assume.
        eapply isBvule_to_isBvsle_pos; auto.
        vm_compute; auto.
        rewrite H0. vm_compute. reflexivity.
      }
      clear - HH. lia.
    + reflexivity.
    + repeat split. 
      eapply e_assume.
    + reflexivity.
    + destruct_conjs; subst.
      clear HPrePost HWf. lia.
    + destruct_conjs; subst. auto.
    + unfold zero_array_precond in *; destruct_conjs; subst; hnf; split.
      * solve_bv_no_overflow. 
      * split; auto.
        solve_bv_no_overflow.
    + reflexivity.
    + unfold zero_array_precond, zero_array_invariant in *.
      destruct_conjs; subst.
      subst.
      hnf.
      rewrite and_bool_eq_false in *.
      exfalso.
      destruct e_if0 as [e_if0 | e_if0].
      * eapply isBvslt_def_opp in e_if0.
        rewrite <- i1 in e_if0.
        vm_compute in e_if0; congruence.
      * eapply isBvslt_def_opp in e_if0.
        rewrite -> i2 in e_if0.
        rewrite -> i0 in e_if0.
        vm_compute in e_if0. congruence.
    + reflexivity.
      
      Unshelve.
      all: auto.
      
Qed.


Definition contains0_precond l
  := isBvsle 64 (intToBv 64 0) l /\ isBvsle 64 l bvMem_hi.

Definition contains0_invariant l l' i
  := isBvsle 64 (intToBv 64 0) i /\ isBvsle 64 i l /\ l = l'.

(* This proof is *identical* to no_errors_zero_array except for in the one noted spot *)
Lemma no_errors_contains0
  : refinesFun contains0 (fun x _ => assumingM (contains0_precond x) noErrorsSpec).
Proof.
  unfold contains0, contains0__tuple_fun, contains0_precond.
  prove_refinement_match_letRecM_l.
  - exact (fun a' i _ _ _ _ _ => assumingM (contains0_invariant a a' i) noErrorsSpec).
  unfold contains0_invariant, noErrorsSpec.
  fold bvMem_lo; fold bvMem_hi.
  time "no_errors_contains0" prove_refinement.
  all: try assumption.
  (* Different from no_errors_zero_array - this used to be taken care of by `prove_refinement`!
     (FIXME Figure out why this fails to be automated here but not above.) *)
  - rewrite e_if in e_maybe.
    discriminate e_maybe.
  - transitivity a2.
    + assumption.
    + apply isBvsle_suc_r; eauto.
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

Definition sum_2d_invariant1 (l1 l1' l2 l2' i j : bitvector 64)
  := isBvsle 64 (intToBv 64 0) i /\ isBvslt 64 i l1 /\ l1 = l1' /\
     isBvsle 64 (intToBv 64 0) j /\ isBvsle 64 j l2 /\ l2 = l2'.

Definition sum_2d_invariant2 (l1 l1' l2 l2' i : bitvector 64)
  := isBvsle 64 (intToBv 64 0) i /\ isBvsle 64 i l1 /\ l1 = l1' /\ l2 = l2'.

Lemma no_errors_sum_2d
  : refinesFun sum_2d (fun l1 l2 _ => assumingM (sum_2d_precond l1 l2) noErrorsSpec).
Proof.
  unfold sum_2d, sum_2d__tuple_fun, sum_2d_precond.
  time "no_errors_sum_2d (1/2)" prove_refinement_match_letRecM_l.
  - exact (fun a' a0' i j _ _ _ _ _ _ _ => assumingM (sum_2d_invariant1 a a' a0 a0' i j) noErrorsSpec).
Admitted.
(*   - exact (fun a' a0' i => assumingM (sum_2d_invariant2 a a' a0 a0' i) noErrorsSpec). *)
(*   unfold sum_2d_invariant1, sum_2d_invariant2, noErrorsSpec. *)
(*   fold bvMem_lo; fold bvMem_hi. *)
(*   time "no_errors_sum_2d (2/2)" prove_refinement. *)
(*   all: try assumption. *)
(*   * rewrite <- isBvult_to_isBvslt_pos in e_assuming4; try assumption. *)
(*     rewrite e_assuming4 in e_maybe. *)
(*     discriminate e_maybe. *)
(*   * rewrite <- isBvsle_suc_r; try assumption. *)
(*     rewrite e_assuming6, e_assuming2. *)
(*     reflexivity. *)
(*   * apply isBvslt_to_isBvsle_suc, isBvult_to_isBvslt_pos; assumption. *)
(*   * rewrite <- e_assuming5 in e_if2. *)
(*     vm_compute in e_if2; inversion e_if2. *)
(*   * rewrite e_assuming6, e_assuming2 in e_if2. *)
(*     apply isBvslt_antirefl in e_if2; inversion e_if2. *)
(*   * rewrite <- e_assuming3 in e_if0. *)
(*     vm_compute in e_if0; inversion e_if0. *)
(*   * rewrite e_assuming4, e_assuming0 in e_if0. *)
(*     apply isBvslt_antirefl in e_if0; inversion e_if0. *)
(*   * rewrite e_assuming3. *)
(*     apply isBvsle_suc_r, isBvslt_to_isBvsle. *)
(*     rewrite e_assuming4, e_assuming0. *)
(*     reflexivity. *)
(*   * apply isBvslt_to_isBvsle_suc; assumption. *)
(*   * apply isBvult_to_isBvslt_pos; assumption. *)
(* Qed. *)


Definition sum_inc_ptr_invar (len0 idx len : bitvector 64) :=
  isBvule 64 idx len0 /\ len = bvSub 64 len0 idx.

Lemma no_errors_sum_inc_ptr : refinesFun sum_inc_ptr (fun len arr => noErrorsSpec).
Proof.
  unfold sum_inc_ptr, sum_inc_ptr__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun len0 idx len sum arr _ _ _ => assumingM (sum_inc_ptr_invar len0 idx len) noErrorsSpec).
  unfold noErrorsSpec, sum_inc_ptr_invar.
  time "no_errors_sum_inc_ptr" prove_refinement.
  all: try assumption.
  (*
  - assert (isBvult 64 a2 a1).
    + apply isBvule_to_isBvult_or_eq in e_assuming.
      destruct e_assuming; [assumption |].
      apply bvEq_bvSub_r in H.
      (* symmetry in H; contradiction. *) admit.
    + rewrite H in e_maybe; discriminate e_maybe.
  - apply isBvult_to_isBvule_suc; assumption.
  - repeat rewrite bvSub_eq_bvAdd_neg.
    rewrite bvAdd_assoc; f_equal.
    rewrite bvNeg_bvAdd_distrib; reflexivity.
  - apply isBvule_zero_n.
  - symmetry; apply bvSub_n_zero.
  *)
Admitted.
(* Qed. *)


Definition sum_inc_ptr_spec len : BVVec 64 len (bitvector 8) -> bitvector 64 :=
  foldr _ _ _ (fun a b => bvAdd 64 b (bvUExt 56 8 a)) (intToBv 64 0).

Definition sum_inc_ptr_letRec_spec len0 idx len (sum : bitvector 64) arr (_ _ _ : unit) :=
  forallM (fun (pf : isBvule 64 idx len0) =>
  assumingM (len = bvSub 64 len0 idx)
            (returnM (arr, bvAdd 64 sum (sum_inc_ptr_spec (bvSub 64 len0 idx)
                                                     (dropBVVec _ _ _ idx pf arr))))).

Lemma sum_inc_ptr_spec_ref :
  refinesFun sum_inc_ptr (fun len arr => returnM (arr, sum_inc_ptr_spec len arr)).
Proof.
  unfold sum_inc_ptr, sum_inc_ptr__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact sum_inc_ptr_letRec_spec.
  unfold noErrorsSpec, sum_inc_ptr_letRec_spec, sum_inc_ptr_spec.
  time "sum_inc_ptr_spec_ref" prove_refinement.
  (* Why didn't prove_refinement do this? *)
  3: prove_refinement_eauto; [| apply refinesM_returnM ].
  7: prove_refinement_eauto; [| apply refinesM_returnM ].
  (* same as no_errors_sum_inc_ptr *)
  (*
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
  (* same as no_errors_sum_inc_ptr *)
  - apply isBvule_zero_n.
  - symmetry; apply bvSub_n_zero.
  (* unique to this proof *)
  - rewrite bvAdd_id_l.
    repeat f_equal.
    admit. *)
Admitted.

(* We *really* need a better bitvector library, the lemmas we need are getting pretty ad-hoc *)

Axiom isBvsle_bvSub_inj_pos : forall w a b c, isBvsle w (intToBv w 0) a ->
                                              isBvsle w (intToBv w 0) b ->
                                              isBvsle w (intToBv w 0) c ->
                                              isBvsle w (bvSub w a c) (bvSub w b c) <->
                                              isBvsle w a b.

Definition even_odd_sums_diff_invar half_len len i :=
  len = bvMul 64 (intToBv 64 2) half_len /\
  isBvslt 64 (intToBv 64 0) i.

Lemma no_errors_even_odd_sums_diff :
  refinesFun even_odd_sums_diff (fun half_len arr => noErrorsSpec).
Proof.
  unfold even_odd_sums_diff, even_odd_sums_diff__tuple_fun.
  Set Printing Depth 1000.
  prove_refinement_match_letRecM_l.
  - exact (fun half_len len sum i arr _ _ _ _ =>
             assumingM (even_odd_sums_diff_invar half_len len i)
                       noErrorsSpec).
  unfold even_odd_sums_diff_invar, noErrorsSpec.
  time "even_odd_sums_diff" prove_refinement.
  all: try assumption.
  - enough (isBvult 64 a2 (bvMul 64 (intToBv 64 2) a1))
      by (rewrite H in e_maybe; discriminate e_maybe).
    rewrite <- e_if.
    assert (isBvsle 64 (intToBv 64 0) a4) by (apply isBvslt_to_isBvsle; eauto).
    apply isBvult_to_isBvslt_pos; eauto.
    + change (intToBv 64 0) with (bvSub 64 (intToBv 64 1) (intToBv 64 1)).
      (* apply isBvsle_bvSub_inj_pos. *)
      (* I give up I'm done messing around manually with bitvectors for now *)
      admit.
    + rewrite e_let.
      apply isBvslt_pred_l; eauto.
      rewrite <- e_assuming; reflexivity.
  - (* (e_if4 is a contradiction) *)
    admit.
  - admit.
  - rewrite e_assuming.
    change (intToBv 64 2) with (bvAdd 64 (intToBv 64 1) (intToBv 64 1)).
    rewrite <- bvAdd_assoc.
    rewrite <- isBvslt_suc_r.
    + admit.
    + admit.
Admitted.
