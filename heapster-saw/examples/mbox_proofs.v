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
  unfoldMbox (Mbox_cons strt len m d) = Right _ _ (strt, (len, (m, (d, tt)))) :=
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
  g (strt, (len, (m, (d, tt)))) |= P ->
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


Lemma no_errors_mbox_drop
  : refinesFun mbox_drop (fun _ _ => noErrorsSpec).
Proof.
  unfold mbox_drop, mbox_drop__tuple_fun, noErrorsSpec.
  (* Set Ltac Profiling. *)
  time "no_errors_mbox_drop" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.

Definition mbox_drop_spec : Mbox -> BV64 -> Mbox :=
  Mbox__rec _ (fun _ => Mbox_nil) (fun strt len next rec d ix =>
    if bvuge 64 (projT1 ix) (projT1 len)
    then Mbox_cons (existT _ (intToBv 64 0) tt) (existT _ (intToBv 64 0) tt)
                   (rec (existT _ (bvSub 64 (projT1 ix) (projT1 len)) tt)) d
    else Mbox_cons (existT _ (bvAdd 64 (projT1 ix) (projT1 strt)) tt)
                   (existT _ (bvSub 64 (projT1 len) (projT1 ix)) tt) next d).

Lemma mbox_drop_spec_ref
  : refinesFun mbox_drop (fun x ix => returnM (mbox_drop_spec x ix)).
Proof.
  unfold mbox_drop, mbox_drop__tuple_fun, mbox_drop_spec.
  (* Set Ltac Profiling. *)
  time "mbox_drop_spec_ref" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.


Lemma mbox_free_chain_spec_ref
  : refinesFun mbox_free_chain (fun _ => returnM (mkBV32 (intToBv 32 0))).
Proof.
  unfold mbox_free_chain, mbox_free_chain__tuple_fun, mboxFreeSpec.
  prove_refinement_match_letRecM_l.
  - exact (fun _ => returnM (mkBV32 (intToBv 32 0))).
  unfold mkBV32.
  (* Set Ltac Profiling. *)
  time "mbox_free_chain_spec_ref" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
Time Qed.

Lemma no_errors_mbox_free_chain
  : refinesFun mbox_free_chain (fun _ => noErrorsSpec).
Proof.
  rewrite mbox_free_chain_spec_ref.
  unfold noErrorsSpec, mkBV32.
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
  time "mbox_concat_spec_ref" prove_refinement.
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

Definition mbox_detach_spec : Mbox -> Mbox * (Mbox * unit) :=
  Mbox__rec _ (Mbox_nil, (Mbox_nil, tt))
            (fun strt len next _ d => (next, (Mbox_cons strt len Mbox_nil d, tt))).

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
          (fun strt len m rec d => bvAdd 64 rec (projT1 len)).

Lemma mbox_len_spec_ref
  : refinesFun mbox_len (fun m => returnM (m, (existT _ (mbox_len_spec m) tt, tt))).
Proof.
  unfold mbox_len, mbox_len__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun m1 rec m2 => returnM (transMbox m1 m2, (existT _ (bvAdd 64 (projT1 rec) (mbox_len_spec m2)) tt, tt))).
  unfold mbox_len_spec.
  (* Set Ltac Profiling. *)
  time "mbox_len_spec_ref" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
  (* Most of the remaining cases are taken care of with just bvAdd_id_l and bvAdd_id_r *)
  all: try rewrite bvAdd_id_r; try rewrite bvAdd_id_l; try reflexivity.
  (* The remaining case just needs a few more rewrites *)
  - do 3 f_equal.
    rewrite bvAdd_assoc; f_equal.
    rewrite bvAdd_comm; reflexivity.
  - cbn; rewrite transMbox_Mbox_nil_r; reflexivity.
Time Qed.


Definition mbox_copy_precond : Mbox -> Prop :=
  Mbox__rec (fun _ => Prop) True (fun strt len _ _ _ =>
    isBvslt 64 (intToBv 64 0) (projT1 strt) /\ isBvule 64 (projT1 strt) (intToBv 64 128) /\
    isBvule 64 (projT1 len) (bvSub 64 (intToBv 64 128) (projT1 strt))).

(* This proof takes a *long* time. Since we're also going to prove spec_ref, we
   can prove no-errors faster using that proof (see below) *)
(* Lemma no_errors_mbox_copy *)
(*   : refinesFun mbox_copy (fun m => assumingM (mbox_copy_precond m) noErrorsSpec). *)
(* Proof. *)
(*   unfold mbox_copy, mbox_copy__tuple_fun, mbox_copy_precond, noErrorsSpec. *)
(*   unfold mboxNewSpec, mkBV8, mkBV64. *)
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
(* Time Qed. (* Holy crap this takes a long time! *) *)

Definition empty_mbox_d := genBVVec 64 (intToBv 64 128) BV8 (fun i _ => mkBV8 (bvNat 8 0)).

(* TODO give this a better name and explain what it does *)
Definition conjSliceBVVec (start len : BV64) pf0 pf1 d0 d1 : BVVec 64 bv64_128 BV8 :=
  updSliceBVVec 64 (intToBv 64 128) _ d0 (projT1 start) (projT1 len)
    (sliceBVVec 64 (intToBv 64 128) _ (projT1 start) (projT1 len) pf0 pf1 d1).

(* Given a `start`, `len`, and `dat` of a single Mbox, return an mbox chain consisting of
   a single mbox with `id` 0,  the given `start` and `len`, and the given `dat` with the
   range 0 to `start` zeroed out. *)
Definition mbox_copy_spec_cons strt len m d : CompM (Mbox * (Mbox * unit)) :=
  assumingM (isBvslt 64 (intToBv 64 0) (projT1 strt))
    (forallM (fun pf0 : isBvule 64 (projT1 strt) (intToBv 64 128) =>
      (forallM (fun pf1 : isBvule 64 (projT1 len) (bvSub 64 (intToBv 64 128) (projT1 strt)) =>
        returnM (Mbox_cons strt len m
                           (conjSliceBVVec strt len pf0 pf1 d d),
                (Mbox_cons strt len Mbox_nil
                           (conjSliceBVVec strt len pf0 pf1 empty_mbox_d d), tt)))))).

Definition mbox_copy_spec : Mbox -> CompM (Mbox * (Mbox * unit)) :=
  Mbox__rec (fun _ => CompM  (Mbox * (Mbox * unit))) (returnM (Mbox_nil, (Mbox_nil, tt)))
          (fun strt len m _ d => mbox_copy_spec_cons strt len m d).

Lemma mbox_copy_spec_ref : refinesFun mbox_copy mbox_copy_spec.
Proof.
  unfold mbox_copy, mbox_copy__tuple_fun, mbox_copy_spec, mbox_copy_spec_cons, empty_mbox_d.
  unfold mboxNewSpec, mkBV8, mkBV64.
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
    destruct strt, len, u, u0; cbn.
    unfold conjSliceBVVec; simpl projT1.
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
Time Qed. (* FIXME The QED takes longer than the proof itself!! *)

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
