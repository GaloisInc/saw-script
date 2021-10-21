From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

(* All of this for BoolDecidableEqDepSet.UIP, from:
   https://stackoverflow.com/questions/50924127/record-equality-in-coq *)
From Coq Require Import Logic.Eqdep_dec.
Module BoolDecidableSet <: DecidableSet.
Definition U := bool.
Definition eq_dec := Bool.bool_dec.
End BoolDecidableSet.
Module BoolDecidableEqDepSet := DecidableEqDepSet BoolDecidableSet.

Require Import Examples.mbox_gen.
Import mbox.

Import SAWCorePrelude.


Definition unfoldMbox_nil :
  unfoldMbox Mbox_nil = Left _ _ tt :=
  reflexivity _.
Definition unfoldMbox_cons strt len m d :
  unfoldMbox (Mbox_cons strt len m d) = Right _ _ (strt, (len, (m, d))) :=
  reflexivity _.

Ltac Mbox_destruct m m' := destruct m as [| ?strt ?len m' ?d].
Ltac Mbox_induction m m' := induction m as [| ?strt ?len m' ? ?d].
Ltac Mbox_simpl := try rewrite unfoldMbox_nil; try rewrite unfoldMbox_cons; simpl Mbox__rec in *.
                   (* simpl unfoldMbox in *; simpl foldMbox in *; simpl Mbox__rec in *. *)

Lemma refinesM_either_unfoldMbox_nil_l {C} f g (P : CompM C) :
  f tt |= P ->
  SAWCorePrelude.either _ _ _ f g (unfoldMbox Mbox_nil) |= P.
Proof. eauto. Qed.

Lemma refinesM_either_unfoldMbox_cons_l {C} strt len m d f g (P : CompM C) :
  g (strt, (len, (m, d))) |= P ->
  SAWCorePrelude.either _ _ _ f g (unfoldMbox (Mbox_cons strt len m d)) |= P.
Proof. eauto. Qed.

Ltac either_unfoldMbox m :=
  lazymatch m with
  | Mbox_nil =>
    simple apply refinesM_either_unfoldMbox_nil_l
  | Mbox_cons ?strt ?len ?m0 ?d =>
    simple apply (refinesM_either_unfoldMbox_cons_l strt len m0 d)
  | _ => let strt := fresh "strt" in
         let len  := fresh "len" in
         let m0   := fresh m in
         let d    := fresh "d" in destruct m as [| strt len m0 d ];
                                  [ either_unfoldMbox Mbox_nil
                                  | either_unfoldMbox (Mbox_cons strt len m0 d) ];
                                  simpl foldMbox; simpl Mbox__rec in *; unfold_projs
  end.

Hint Extern 0 (SAWCorePrelude.either _ _ _ _ _ (unfoldMbox ?m) |= _) =>
  either_unfoldMbox m : refinesM.
Hint Extern 0 (_ |= SAWCorePrelude.either _ _ _ _ _ (unfoldMbox ?m)) =>
  either_unfoldMbox m : refinesM.

Lemma transMbox_Mbox_nil_r m : transMbox m Mbox_nil = m.
Proof.
  induction m; eauto.
  simpl; f_equal; eauto.
Qed.

Lemma transMbox_assoc m1 m2 m3 :
  transMbox (transMbox m1 m2) m3 = transMbox m1 (transMbox m2 m3).
Proof.
  induction m1; eauto.
  simpl; f_equal; eauto.
Qed.

Hint Rewrite transMbox_Mbox_nil_r transMbox_assoc : refinesM.


(* ========================================================================== *)


Definition mbox_randomize_precond : Mbox -> Prop :=
  Mbox__rec (fun _ => Prop) True (fun strt len _ _ _ =>
    (* 0 <= strt <= len < 128 *)
    isBvsle 64 (intToBv 64 0) strt /\ isBvsle 64 strt len /\
    isBvslt 64 len (intToBv 64 128)).

Definition mbox_randomize_invar (strt len i : bitvector 64) : Prop :=
  (* 0 <= strt <= i <= len < 128 *)
  isBvsle 64 (intToBv 64 0) strt /\ isBvsle 64 strt i /\
  isBvsle 64 i len /\ isBvslt 64 len (intToBv 64 128).

Lemma no_errors_mbox_randomize
  : refinesFun mbox_randomize (fun m => assumingM (mbox_randomize_precond m) noErrorsSpec).
Proof.
  unfold mbox_randomize, mbox_randomize__tuple_fun, mbox_randomize_precond.
  prove_refinement_match_letRecM_l.
  - exact (fun strt len m d i => assumingM (mbox_randomize_invar strt len i) noErrorsSpec).
  unfold noErrorsSpec, randSpec, mbox_randomize_invar.
  time "no_errors_mbox_randomize" prove_refinement.
  (* All the `Mbox_def` and `Vec 32 bool` goals are only every used in *)
  (* impossible cases, so they can be set to whatever Coq chooses. These *)
  (* calls to `assumption` also take care of showing that the loop invariant *)
  (* holds initially from our precondition, and a few of the cases of showing *)
  (* that the loop invariant holds inductively (see below). *)
  all: try assumption.
  (* Showing the error case of the array bounds check is impossible by virtue *)
  (* of our loop invariant *)
  - assert (isBvsle 64 (intToBv 64 0) a4) by (rewrite e_assuming0; eauto).
    assert (isBvsle 64 (intToBv 64 0) a1) by (rewrite H; eauto).
    apply isBvult_to_isBvslt_pos in e_if; eauto.
    assert (isBvult 64 a4 (intToBv 64 128)).
    + apply isBvult_to_isBvslt_pos; [ eauto | reflexivity | ].
      rewrite e_if; eauto.
    + rewrite H1 in e_maybe; discriminate e_maybe.
  (* Showing the loop invariant holds inductively (the remaining two cases) *)
  - rewrite e_assuming1; apply isBvsle_suc_r.
    apply isBvslt_to_isBvsle.
    rewrite e_assuming2, e_assuming3.
    reflexivity.
  - apply isBvslt_to_isBvsle_suc.
    apply isBvult_to_isBvslt_pos in e_if.
    + assumption.
    + rewrite e_assuming0; eauto.
    + rewrite e_assuming0, e_assuming1; eauto.
  (* Showing the error case of the overflow check is impossible by virtue of *)
  (* our loop invariant *)
  - rewrite <- e_assuming1, <- e_assuming0 in e_if0.
    vm_compute in e_if0; discriminate e_if0.
  - rewrite e_assuming2, e_assuming3 in e_if0.
    vm_compute in e_if0; discriminate e_if0.
Qed.

(*
  In English, the spec for `mbox_randomize m` is:
  - If `m` is non-null, the function returns `SUCCESS` and `m->data` is set to
    some `data'` such that `m->data[i] = data'[i]` for all `i` such that
    `i < m->strt` or `i >= m->len`.
  - Otherwise, the function returns MBOX_NULL_ERROR.
*)

Definition SUCCESS         := intToBv 32 0.
Definition MBOX_NULL_ERROR := intToBv 32 23.

Definition mbox_randomize_non_null_spec strt len m d : CompM (Mbox * bitvector 32) :=
  existsM (fun d' => assertM (forall i (pf : isBvult 64 i bv64_128),
                                isBvslt 64 i strt \/ isBvsle 64 len i ->
                                atBVVec _ _ _ d i pf = atBVVec _ _ _ d' i pf) >>
                     returnM (Mbox_cons strt len m d', SUCCESS)).

Definition mbox_randomize_spec : Mbox -> CompM (Mbox * bitvector 32) :=
  Mbox__rec (fun _ => CompM (Mbox * bitvector 32))
          (returnM (Mbox_nil, MBOX_NULL_ERROR))
          (fun strt len m _ d => mbox_randomize_non_null_spec strt len m d).

Lemma mbox_randomize_spec_ref :
  refinesFun mbox_randomize (fun m => assumingM (mbox_randomize_precond m) (mbox_randomize_spec m)).
Proof.
  unfold mbox_randomize, mbox_randomize__tuple_fun, mbox_randomize_precond, mbox_randomize_spec.
  prove_refinement_match_letRecM_l.
  - exact (fun strt len m d i =>
             assumingM (mbox_randomize_invar strt len i)
                       (mbox_randomize_non_null_spec strt len m d)).
  unfold noErrorsSpec, randSpec, mbox_randomize_invar.
  time "mbox_randomize_spec_ref" prove_refinement.
  (* All but the noted cases are the same as `no_errors_mbox_randomize` above *)
  all: try assumption.
  (* Showing the error case of the array bounds check is impossible by virtue *)
  (* of our loop invariant *)
  - assert (isBvsle 64 (intToBv 64 0) a4) by (rewrite e_assuming0; eauto).
    assert (isBvsle 64 (intToBv 64 0) a1) by (rewrite H; eauto).
    apply isBvult_to_isBvslt_pos in e_if; eauto.
    assert (isBvult 64 a4 (intToBv 64 128)).
    + apply isBvult_to_isBvslt_pos; [ eauto | reflexivity | ].
      rewrite e_if; eauto.
    + rewrite H1 in e_maybe; discriminate e_maybe.
  (* Showing the loop invariant holds inductively (the remaining two cases) *)
  - rewrite e_assuming1; apply isBvsle_suc_r.
    apply isBvslt_to_isBvsle.
    rewrite e_assuming2, e_assuming3.
    reflexivity.
  - apply isBvslt_to_isBvsle_suc.
    apply isBvult_to_isBvslt_pos in e_if.
    + assumption.
    + rewrite e_assuming0; eauto.
    + rewrite e_assuming0, e_assuming1; eauto.
  (* Unique to this proof: Showing our spec works for the recursive case *)
  - rewrite transMbox_Mbox_nil_r; simpl.
    unfold mbox_randomize_non_null_spec.
    prove_refinement.
    + exact e_exists0.
    + prove_refinement; intros.
      rewrite <- e_assert; eauto.
      unfold updBVVec; rewrite at_gen_BVVec.
      enough (bvEq 64 i a4 = false) by (rewrite H0; reflexivity).
      destruct H.
      * apply isBvslt_to_bvEq_false.
        rewrite e_assuming1 in H; eauto.
      * rewrite bvEq_sym.
        apply isBvslt_to_bvEq_false.
        apply isBvult_to_isBvslt_pos in e_if.
        -- rewrite H in e_if; eauto.
        -- rewrite e_assuming0; eauto.
        -- rewrite e_assuming0, e_assuming1; eauto.
  (* Showing the error case of the overflow check is impossible by virtue of *)
  (* our loop invariant *)
  - rewrite <- e_assuming1, <- e_assuming0 in e_if0.
    vm_compute in e_if0; discriminate e_if0.
  - rewrite e_assuming2, e_assuming3 in e_if0.
    vm_compute in e_if0; discriminate e_if0.
  (* Unique to this proof: Showing our spec works for the base case *)
  - rewrite transMbox_Mbox_nil_r; simpl.
    unfold mbox_randomize_non_null_spec.
    prove_refinement.
    + exact a3.
    + prove_refinement.
Qed.


Lemma no_errors_mbox_drop
  : refinesFun mbox_drop (fun _ _ => noErrorsSpec).
Proof.
  unfold mbox_drop, mbox_drop__tuple_fun, noErrorsSpec.
  (* Set Ltac Profiling. *)
  time "no_errors_mbox_drop" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.

Definition mbox_drop_spec : Mbox -> bitvector 64 -> Mbox :=
  Mbox__rec _ (fun _ => Mbox_nil) (fun strt len next rec d ix =>
    if bvuge 64 ix len
    then Mbox_cons (intToBv 64 0) (intToBv 64 0) (rec (bvSub 64 ix len)) d
    else Mbox_cons (bvAdd 64 ix strt) (bvSub 64 len ix) next d).

Lemma mbox_drop_spec_ref
  : refinesFun mbox_drop (fun x ix => returnM (mbox_drop_spec x ix)).
Proof.
  unfold mbox_drop, mbox_drop__tuple_fun, mbox_drop_spec.
  (* Set Ltac Profiling. *)
  time "mbox_drop_spec_ref" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.


Lemma mbox_free_chain_spec_ref
  : refinesFun mbox_free_chain (fun _ => returnM (intToBv 32 0)).
Proof.
  unfold mbox_free_chain, mbox_free_chain__tuple_fun, mboxFreeSpec.
  prove_refinement_match_letRecM_l.
  - exact (fun _ => returnM (intToBv 32 0)).
  (* Set Ltac Profiling. *)
  time "mbox_free_chain_spec_ref" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.

Lemma no_errors_mbox_free_chain
  : refinesFun mbox_free_chain (fun _ => noErrorsSpec).
Proof.
  rewrite mbox_free_chain_spec_ref.
  unfold noErrorsSpec.
  prove_refinement.
Qed.


Lemma no_errors_mbox_concat
  : refinesFun mbox_concat (fun _ _ => noErrorsSpec).
Proof.
  unfold mbox_concat, mbox_concat__tuple_fun, noErrorsSpec.
  (* Set Ltac Profiling. *)
  time "no_errors_mbox_concat" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.

Definition mbox_concat_spec (x y : Mbox) : Mbox :=
  Mbox__rec _ Mbox_nil (fun strt len _ _ d => Mbox_cons strt len y d) x.

Lemma mbox_concat_spec_ref
  : refinesFun mbox_concat (fun x y => returnM (mbox_concat_spec x y)).
Proof.
  unfold mbox_concat, mbox_concat__tuple_fun, mbox_concat_spec.
  (* Set Ltac Profiling. *)
  time "mbox_concat_spec_ref" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.

(* Add `mbox_concat_spec_ref` to the hint database. Unfortunately, Coq will not unfold refinesFun
   and mbox_concat_spec when rewriting, and the only workaround I know right now is this :/ *)
Definition mbox_concat_spec_ref' : ltac:(let tp := type of mbox_concat_spec_ref in
                                         let tp' := eval unfold refinesFun, mbox_concat_spec in tp
                                          in exact tp') := mbox_concat_spec_ref.
Hint Rewrite mbox_concat_spec_ref' : refinement_proofs.


Lemma no_errors_mbox_concat_chains
  : refinesFun mbox_concat_chains (fun _ _ => noErrorsSpec).
Proof.
  unfold mbox_concat_chains, mbox_concat_chains__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun _ _ _ _ _ _ => noErrorsSpec).
  unfold noErrorsSpec.
  (* Set Ltac Profiling. *)
  time "no_errors_mbox_concat_chains" prove_refinement with NoRewrite.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.

Definition mbox_concat_chains_spec (x y : Mbox) : Mbox :=
  Mbox__rec (fun _ => Mbox) Mbox_nil (fun _ _ _ _ _ =>
    Mbox__rec (fun _ => Mbox) x (fun _ _ _ _ _ =>
      transMbox x y) y) x.

Lemma mbox_concat_chains_spec_ref
  : refinesFun mbox_concat_chains (fun x y => returnM (mbox_concat_chains_spec x y)).
Proof.
  unfold mbox_concat_chains, mbox_concat_chains__tuple_fun.
  prove_refinement_match_letRecM_l.
  - intros x y strt len next d.
    exact (returnM (transMbox x (Mbox_cons strt len (transMbox next y) d))).
  unfold mbox_concat_chains_spec.
  time "mbox_concat_chains_spec_ref" prove_refinement.
  simpl; repeat rewrite transMbox_Mbox_nil_r; reflexivity.
Time Qed.


Lemma no_errors_mbox_detach
  : refinesFun mbox_detach (fun _ => noErrorsSpec).
Proof.
  unfold mbox_detach, mbox_detach__tuple_fun, noErrorsSpec.
  (* Set Ltac Profiling. *)
  time "no_errors_mbox_detach" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.

Definition mbox_detach_spec : Mbox -> Mbox * Mbox :=
  Mbox__rec _ (Mbox_nil, Mbox_nil)
            (fun strt len next _ d => (next, (Mbox_cons strt len Mbox_nil d))).

Lemma mbox_detach_spec_ref
  : refinesFun mbox_detach (fun x => returnM (mbox_detach_spec x)).
Proof.
  unfold mbox_detach, mbox_detach__tuple_fun, mbox_detach, mbox_detach_spec.
  (* Set Ltac Profiling. *)
  time "mbox_detach_spec_ref" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.

(* Add `mbox_detach_spec_ref` to the hint database. Unfortunately, Coq will not unfold refinesFun
   and mbox_detach_spec when rewriting, and the only workaround I know right now is this :/ *)
Definition mbox_detach_spec_ref' : ltac:(let tp := type of mbox_detach_spec_ref in
                                         let tp' := eval unfold refinesFun, mbox_detach_spec in tp
                                          in exact tp') := mbox_detach_spec_ref.
Hint Rewrite mbox_detach_spec_ref' : refinement_proofs.


Lemma no_errors_mbox_len
  : refinesFun mbox_len (fun _ => noErrorsSpec).
Proof.
  unfold mbox_len, mbox_len__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun _ _ _ => noErrorsSpec).
  unfold noErrorsSpec.
  (* Set Ltac Profiling. *)
  time "no_errors_mbox_len" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.

Definition mbox_len_spec : Mbox -> bitvector 64 :=
  Mbox__rec (fun _ =>  bitvector 64) (intToBv 64 0)
          (fun strt len m rec d => bvAdd 64 rec len).

Lemma mbox_len_spec_ref
  : refinesFun mbox_len (fun m => returnM (m, mbox_len_spec m)).
Proof.
  unfold mbox_len, mbox_len__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun m1 rec m2 => returnM (transMbox m1 m2, bvAdd 64 rec (mbox_len_spec m2))).
  unfold mbox_len_spec.
  (* Set Ltac Profiling. *)
  time "mbox_len_spec_ref" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
  (* Most of the remaining cases are taken care of with just bvAdd_id_l and bvAdd_id_r *)
  all: try rewrite bvAdd_id_r; try rewrite bvAdd_id_l; try reflexivity.
  (* The remaining case just needs a few more rewrites *)
  - f_equal.
    rewrite bvAdd_assoc; f_equal.
    rewrite bvAdd_comm; reflexivity.
  - cbn; rewrite transMbox_Mbox_nil_r; reflexivity.
Time Qed.


Definition mbox_copy_precond : Mbox -> Prop :=
  Mbox__rec (fun _ => Prop) True (fun strt len _ _ _ =>
    isBvslt 64 (intToBv 64 0) strt /\ isBvule 64 strt (intToBv 64 128) /\
    isBvule 64 len (bvSub 64 (intToBv 64 128) strt)).

(* This proof takes a bit to complete. Since we're also going to prove spec_ref,
   we can prove no-errors faster using that proof (see below) *)
(* Lemma no_errors_mbox_copy *)
(*   : refinesFun mbox_copy (fun m => assumingM (mbox_copy_precond m) noErrorsSpec). *)
(* Proof. *)
(*   unfold mbox_copy, mbox_copy__tuple_fun, mboxNewSpec. *)
(*   unfold mbox_copy_precond, noErrorsSpec. *)
(*   (* Yikes! The below functions may or may not be defined depending on what *)
(*      machine compiled mbox.bc *) *)
(*   try unfold llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64. *)
(*   try unfold llvm__x2eobjectsize__x2ei64__x2ep0i8, __memcpy_chk. *)
(*   Set Printing Depth 1000. *)
(*   time "no_errors_mbox_copy" prove_refinement with NoRewrite. *)
(*   all: try assumption. *)
(*   - rewrite e_assuming0 in e_maybe. *)
(*     discriminate e_maybe. *)
(*   - rewrite e_assuming1 in e_maybe0. *)
(*     discriminate e_maybe0. *)
(*   - rewrite a in e_maybe1. *)
(*     discriminate e_maybe1. *)
(*   - rewrite e_assuming1 in e_maybe2. *)
(*     discriminate e_maybe2. *)
(*   - rewrite <- e_assuming in e_if. *)
(*     vm_compute in e_if; discriminate e_if. *)
(*   - rewrite <- isBvult_to_isBvslt_pos in e_if. *)
(*     + rewrite e_assuming0 in e_if. *)
(*       vm_compute in e_if; discriminate e_if. *)
(*     + reflexivity. *)
(*     + apply isBvslt_to_isBvsle. *)
(*       assumption. *)
(* Time Qed. *)

Definition empty_mbox_d := genBVVec 64 (intToBv 64 128) (bitvector 8) (fun i _ => bvNat 8 0).

(* TODO give this a better name and explain what it does *)
Definition conjSliceBVVec (strt len : bitvector 64) pf0 pf1 d0 d1 : BVVec 64 bv64_128 (bitvector 8) :=
  updSliceBVVec 64 (intToBv 64 128) _ d0 strt len
    (sliceBVVec 64 (intToBv 64 128) _ strt len pf0 pf1 d1).

(* Given a `start`, `len`, and `dat` of a single Mbox, return an mbox chain consisting of
   a single mbox with `id` 0,  the given `start` and `len`, and the given `dat` with the
   range 0 to `start` zeroed out. *)
Definition mbox_copy_spec_cons strt len m d : CompM (Mbox * Mbox) :=
  assumingM (isBvslt 64 (intToBv 64 0) strt)
    (forallM (fun pf0 : isBvule 64 strt (intToBv 64 128) =>
      (forallM (fun pf1 : isBvule 64 len (bvSub 64 (intToBv 64 128) strt) =>
        returnM (Mbox_cons strt len m
                           (conjSliceBVVec strt len pf0 pf1 d d),
                (Mbox_cons strt len Mbox_nil
                           (conjSliceBVVec strt len pf0 pf1 empty_mbox_d d))))))).

Definition mbox_copy_spec : Mbox -> CompM (Mbox * Mbox) :=
  Mbox__rec (fun _ => CompM  (Mbox * Mbox)) (returnM (Mbox_nil, Mbox_nil))
          (fun strt len m _ d => mbox_copy_spec_cons strt len m d).

Lemma mbox_copy_spec_ref : refinesFun mbox_copy mbox_copy_spec.
Proof.
  unfold mbox_copy, mbox_copy__tuple_fun, mboxNewSpec.
  unfold mbox_copy_spec, mbox_copy_spec_cons, empty_mbox_d.
  (* Yikes! The below functions may or may not be defined depending on what
     machine compiled mbox.bc *)
  try unfold llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64.
  try unfold llvm__x2eobjectsize__x2ei64__x2ep0i8, __memcpy_chk.
  Set Printing Depth 1000.
  (* Expect this to take on the order of 15 seconds, removing the `NoRewrite`
     adds another 5 seconds and only simplifies the proof in the one noted spot *)
  (* Set Ltac Profiling. *)
  time "mbox_copy_spec_ref" prove_refinement with NoRewrite.
  (* Show Ltac Profile. Reset Ltac Profile. *)
  all: try discriminate e_either.
  - rewrite e_forall in e_maybe.
    discriminate e_maybe.
  - rewrite e_forall0 in e_maybe0.
    discriminate e_maybe0.
  (* TODO Add the sort of reasoning in the next two cases back into the automation? *)
  - rewrite a in e_maybe1.
    discriminate e_maybe1.
  - rewrite a1 in e_maybe2.
    discriminate e_maybe2.
  - rewrite transMbox_Mbox_nil_r. (* <- this would go away if we removed "NoRewrite" *)
    replace a2 with e_forall; [ replace a3 with e_forall0 | ].
    unfold conjSliceBVVec.
    reflexivity.
  - apply BoolDecidableEqDepSet.UIP.
  - apply BoolDecidableEqDepSet.UIP.
  - rewrite <- e_assuming in e_if.
    vm_compute in e_if; discriminate e_if.
  - rewrite <- isBvult_to_isBvslt_pos in e_if.
    + rewrite e_forall in e_if.
      vm_compute in e_if; discriminate e_if.
    + reflexivity.
    + apply isBvslt_to_isBvsle.
      assumption.
Time Qed.

Lemma no_errors_mbox_copy
  : refinesFun mbox_copy (fun m => assumingM (mbox_copy_precond m) noErrorsSpec).
Proof.
  rewrite mbox_copy_spec_ref.
  unfold mbox_copy_spec, mbox_copy_spec_cons, mbox_copy_precond, noErrorsSpec.
  intro; apply refinesM_assumingM_r; intro e_assuming.
  induction a; simpl in *.
  all: repeat prove_refinement.
Qed.

(* Add `mbox_copy_spec_ref` to the hint database. Unfortunately, Coq will not unfold refinesFun
   and mbox_copy_spec when rewriting, and the only workaround I know right now is this :/ *)
Definition mbox_copy_spec_ref' : ltac:(let tp := type of mbox_copy_spec_ref in
                                       let tp' := eval unfold refinesFun, mbox_copy_spec, mbox_copy_spec_cons, empty_mbox_d in tp
                                        in exact tp') := mbox_copy_spec_ref.
Hint Rewrite mbox_copy_spec_ref' : refinement_proofs.
