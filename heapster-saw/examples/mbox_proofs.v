From Coq          Require Import Lists.List.
From Coq          Require Import Logic.FunctionalExtensionality.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SpecMExtra.
From EnTree       Require Import Automation.
Import SAWCorePrelude.
Import SpecMNotations.
Local Open Scope entree_scope.

(* (* All of this for BoolDecidableEqDepSet.UIP, from:
   https://stackoverflow.com/questions/50924127/record-equality-in-coq *)
From Coq Require Import Logic.Eqdep_dec.
Module BoolDecidableSet <: DecidableSet.
Definition U := bool.
Definition eq_dec := Bool.bool_dec.
End BoolDecidableSet.
Module BoolDecidableEqDepSet := DecidableEqDepSet BoolDecidableSet. *)

Require Import Examples.mbox_gen.
Import mbox.

Local Instance QuantType_Mbox : QuantType Mbox.
Admitted.


(* QOL: nicer names for bitvector and mbox arguments *)
#[local] Hint Extern 901 (IntroArg Any (bitvector _) _) =>
  let e := fresh "x" in IntroArg_intro e : refines prepostcond. 
#[local] Hint Extern 901 (IntroArg Any Mbox _) =>
  let e := fresh "m" in IntroArg_intro e : refines prepostcond. 
#[local] Hint Extern 901 (IntroArg Any Mbox_def _) =>
  let e := fresh "m" in IntroArg_intro e : refines prepostcond.


(* Maybe automation - FIXME move to EnTree.Automation *)

Lemma spec_refines_maybe_l (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  RR A t1 k1 mb (t2 : SpecM E2 Γ2 R2) :
  (mb = Nothing _ -> spec_refines RPre RPost RR t1 t2) ->
  (forall a, mb = Just _ a -> spec_refines RPre RPost RR (k1 a) t2) ->
  spec_refines RPre RPost RR (maybe A (SpecM E1 Γ1 R1) t1 k1 mb) t2.
Proof. destruct mb; intros; eauto. Qed.

Lemma spec_refines_maybe_r (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  RR (t1 : SpecM E1 Γ1 R1) A t2 k2 mb :
  (mb = Nothing _ -> spec_refines RPre RPost RR t1 t2) ->
  (forall a, mb = Just _ a -> spec_refines RPre RPost RR t1 (k2 a)) ->
  spec_refines RPre RPost RR t1 (maybe A (SpecM E2 Γ2 R2) t2 k2 mb).
Proof. destruct mb; intros; eauto. Qed.

Definition spec_refines_maybe_l_IntroArg (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  RR A t1 k1 mb (t2 : SpecM E2 Γ2 R2) :
  (IntroArg Hyp (mb = Nothing _) (fun _ => spec_refines RPre RPost RR t1 t2)) ->
  (IntroArg Any A (fun a => IntroArg Hyp (mb = Just _ a) (fun _ =>
   spec_refines RPre RPost RR (k1 a) t2))) ->
  spec_refines RPre RPost RR (maybe A (SpecM E1 Γ1 R1) t1 k1 mb) t2 :=
  spec_refines_maybe_l E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR A t1 k1 mb t2.

Definition spec_refines_maybe_r_IntroArg (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  RR (t1 : SpecM E1 Γ1 R1) A t2 k2 mb :
  (IntroArg Hyp (mb = Nothing _) (fun _ => spec_refines RPre RPost RR t1 t2)) ->
  (IntroArg Any A (fun a => IntroArg Hyp (mb = Just _ a) (fun _ =>
   spec_refines RPre RPost RR t1 (k2 a)))) ->
  spec_refines RPre RPost RR t1 (maybe A (SpecM E2 Γ2 R2) t2 k2 mb) :=
  spec_refines_maybe_r E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR t1 A t2 k2 mb.

#[global] Hint Extern 101 (spec_refines _ _ _ (maybe _ _ _ _ _) _) =>
  simple apply spec_refines_maybe_l_IntroArg : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ _ (maybe _ _ _ _ _)) =>
  simple apply spec_refines_maybe_r_IntroArg : refines.

Lemma IntroArg_eq_Nothing_const n A (goal : Prop)
  : goal -> IntroArg n (Nothing A = Nothing A) (fun _ => goal).
Proof. intros H eq; eauto. Qed.
Lemma IntroArg_eq_Just_const n A (x y : A) (goal : Prop)
  : IntroArg n (x = y) (fun _ => goal) ->
    IntroArg n (Just A x = Just A y) (fun _ => goal).
Proof. intros H eq; apply H; injection eq; eauto. Qed.
Lemma IntroArg_eq_Nothing_Just n A (x : A) goal
  : IntroArg n (Nothing A = Just A x) goal.
Proof. intros eq; discriminate eq. Qed.
Lemma IntroArg_eq_Just_Nothing n A (x : A) goal
  : IntroArg n (Just A x = Nothing A) goal.
Proof. intros eq; discriminate eq. Qed.

#[global] Hint Extern 101 (IntroArg _ (Nothing _ = Nothing _) _) =>
  simple apply IntroArg_eq_Nothing_const : refines.
#[global] Hint Extern 101 (IntroArg _ (Just _ _ = Just _ _) _) =>
  simple apply IntroArg_eq_Just_const : refines.
#[global] Hint Extern 101 (IntroArg _ (Nothing _ = Just _ _) _) =>
  apply IntroArg_eq_Nothing_Just : refines.
#[global] Hint Extern 101 (IntroArg _ (Just _ _ = Nothing _) _) =>
  apply IntroArg_eq_Just_Nothing : refines.


(* sawLet automation *)

Definition spec_refines_sawLet_const_l (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) A (x : A) t1 t2 :
  spec_refines RPre RPost RR t1 t2 ->
  spec_refines RPre RPost RR (sawLet_def _ _ x (fun _ => t1)) t2 := fun pf => pf.
Definition spec_refines_sawLet_const_r (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) A (x : A) t1 t2 :
  spec_refines RPre RPost RR t1 t2 ->
  spec_refines RPre RPost RR t1 (sawLet_def _ _ x (fun _ => t2)) := fun pf => pf.

Definition spec_refines_sawLet_bv_l_IntroArg (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) w (x : bitvector w) k1 t2 :
  IntroArg Any _ (fun a => IntroArg SAWLet (a = x) (fun _ =>
    spec_refines RPre RPost RR (k1 a) t2)) ->
  spec_refines RPre RPost RR (sawLet_def _ _ x k1) t2.
Proof. intro H; eapply H; eauto. Qed.
Definition spec_refines_sawLet_bv_r_IntroArg (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) w (x : bitvector w) t1 k2 :
  IntroArg Any _ (fun a => IntroArg SAWLet (a = x) (fun _ =>
    spec_refines RPre RPost RR t1 (k2 a))) ->
  spec_refines RPre RPost RR t1 (sawLet_def _ _ x k2).
Proof. intro H; eapply H; eauto. Qed.

Definition spec_refines_sawLet_unfold_l (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) A (x : A) k1 t2 :
  spec_refines RPre RPost RR (k1 x) t2 ->
  spec_refines RPre RPost RR (sawLet_def _ _ x k1) t2 := fun pf => pf.
Definition spec_refines_sawLet_unfold_r (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) A (x : A) t1 k2 :
  spec_refines RPre RPost RR t1 (k2 x) ->
  spec_refines RPre RPost RR t1 (sawLet_def _ _ x k2) := fun pf => pf.

Ltac spec_refines_sawLet_l :=
  first [ simple apply spec_refines_sawLet_const_l
        | simple apply spec_refines_sawLet_bv_l_IntroArg
        | simple apply spec_refines_sawLet_unfold_l ].
Ltac spec_refines_sawLet_r :=
  first [ simple apply spec_refines_sawLet_const_r
        | simple apply spec_refines_sawLet_bv_r_IntroArg
        | simple apply spec_refines_sawLet_unfold_r ].

#[global] Hint Extern 101 (spec_refines _ _ _ (sawLet_def _ _ _ _) _) =>
  spec_refines_sawLet_l : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ _ (sawLet_def _ _ _ _ )) =>
  spec_refines_sawLet_r : refines.


(* bitvector (in)equality automation *)

Lemma simpl_llvm_bool_eq (b : bool) :
  not (bvEq 1 (if b then intToBv 1 (-1) else intToBv 1 0) (intToBv 1 0)) = b.
Proof. destruct b; eauto. Qed.

Definition simpl_llvm_bool_eq_IntroArg n (b1 b2 : bool) (goal : Prop) :
  IntroArg n (b1 = b2) (fun _ => goal) ->
  IntroArg n (not (bvEq 1 (if b1 then intToBv 1 (-1) else intToBv 1 0) (intToBv 1 0)) = b2) (fun _ => goal).
Proof. rewrite simpl_llvm_bool_eq; eauto. Defined.

#[local] Hint Extern 101 (IntroArg _ (not (bvEq 1 (if _ then intToBv 1 (-1) else intToBv 1 0) (intToBv 1 0)) = _) _) =>
  simple eapply simpl_llvm_bool_eq_IntroArg : refines.

Polymorphic Lemma bvuleWithProof_not :
  forall w a b,
  bvuleWithProof w a b = Nothing _ <-> ~ (isBvule w a b).
Proof.
  unfold bvuleWithProof, isBvule.
  split.
  - intros H0 H1.
    rewrite H1 in H0. simpl.
    discriminate.
  - intros H.
    destruct (bvule w a b).
      + contradiction.
      + reflexivity.
Qed.

Polymorphic Lemma bvuleWithProof_not_IntroArg n w a b goal :
  IntroArg n (~ (isBvule w a b)) (fun _ => goal) ->
  IntroArg n (bvuleWithProof w a b = Nothing _) (fun _ => goal).
Proof. intros H eq; apply H; apply bvuleWithProof_not; eauto. Qed.
 
#[local] Hint Extern 101 (IntroArg _ (bvuleWithProof _ _ _ = Nothing _) _) =>
  simple apply bvuleWithProof_not_IntroArg || shelve : refines.

Polymorphic Lemma bvultWithProof_not :
  forall w a b,
  bvultWithProof w a b = Nothing _ <-> ~ (isBvult w a b).
Proof.
  unfold bvultWithProof, isBvult.
  split.
  - intros H0 H1.
    rewrite H1 in H0. simpl.
    discriminate.
  - intros H.
    destruct (bvult w a b).
      + contradiction.
      + reflexivity.
Qed.

Polymorphic Lemma bvultWithProof_not_IntroArg n w a b goal :
  IntroArg n (~ (isBvult w a b)) (fun _ => goal) ->
  IntroArg n (bvultWithProof w a b = Nothing _) (fun _ => goal).
Proof. intros H eq; apply H; apply bvultWithProof_not; eauto. Qed.

#[local] Hint Extern 101 (IntroArg _ (bvultWithProof _ _ _ = Nothing _) _) =>
  apply bvultWithProof_not_IntroArg : refines.

Lemma bvAdd_Sub_cancel w a b :
      bvAdd w a (bvSub w b a) = b.
Proof. holds_for_bits_up_to_3. Qed.

Lemma UIP_bool (x y : bool) (p1 p2 : x = y) : p1 = p2.
Proof.
  apply Eqdep_dec.UIP_dec. apply Bool.bool_dec.
Qed.

Lemma updSlice_slice_identity
        (m : BVVec 64 bv64_128 (bitvector 8))
        (strt len : bitvector 64)
        (pf0 : isBvule 64 strt bv64_128)
        (pf1 : isBvule 64 len (bvSub 64 bv64_128 strt)) :
      updSliceBVVec 64 bv64_128 (bitvector 8) m strt len
        (sliceBVVec 64 bv64_128 (bitvector 8) strt len pf0 pf1 m) = m.
Proof.
  rewrite <- (gen_at_BVVec _ _ _ m) at 3.
  unfold updSliceBVVec.
  f_equal.
  extensionality i. extensionality pf.
  destruct (bvule 64 strt i) eqn:X.
  - destruct (bvultWithProof 64 (bvSub 64 i strt) len) eqn:Y; simpl.
    * reflexivity.
    * unfold sliceBVVec, takeBVVec, dropBVVec.
      do 2 rewrite at_gen_BVVec.
      generalize
        (bvult_sub_add_bvult 64
          (bvSub 64 i strt)
          strt
          bv64_128 pf0
          (trans_bvult_bvule
            64
            (bvSub 64 i strt)
            len
            (bvSub 64 bv64_128 strt)
            e
            pf1)) as H.
    rewrite bvAdd_Sub_cancel. intros H.
    rewrite (UIP_bool _ _ H pf).
    reflexivity.
  - reflexivity.
Qed.

Lemma isBvule_bvSub_remove w a b c :
  isBvule w c b ->
  isBvule w a (bvSub w b c) ->
  isBvule w a b.
Proof. holds_for_bits_up_to_3. Qed.


(* Mbox destruction automation *)

Lemma spec_refines_either_unfoldMbox_nil_l (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) f g (P : SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR (f tt) P ->
  spec_refines RPre RPost RR (either _ _ _ f g (unfoldMbox Mbox_nil)) P.
Proof. eauto. Qed.

Lemma spec_refines_either_unfoldMbox_cons_l (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) strt len m d f g (P : SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR (g (strt, (len, (m, d)))) P ->
  spec_refines RPre RPost RR (either _ _ _ f g (unfoldMbox (Mbox_cons strt len m d))) P.
Proof. eauto. Qed.

Ltac either_unfoldMbox m :=
  lazymatch m with
  | Mbox_nil =>
    simple apply spec_refines_either_unfoldMbox_nil_l
  | Mbox_cons ?strt ?len ?m0 ?d =>
    simple apply (spec_refines_either_unfoldMbox_cons_l _ _ _ _ _ _ _ _ _ strt len m0 d)
  | _ => let strt := fresh "strt" in
         let len  := fresh "len" in
         let m0   := fresh "m" in
         let d    := fresh "d" in destruct m as [| strt len m0 d ];
                                  [ either_unfoldMbox Mbox_nil
                                  | either_unfoldMbox (Mbox_cons strt len m0 d) ];
                                  simpl foldMbox; cbn [ Mbox__rec Mbox_rect ] in *;
                                  unfold SAWCoreScaffolding.fst, SAWCoreScaffolding.snd;
                                  cbn [ Datatypes.fst Datatypes.snd projT1 ]
  end.

Global Hint Extern 100 (spec_refines _ _ _ (either _ _ _ _ _ (unfoldMbox ?m)) _) =>
  either_unfoldMbox m : refines.
Global Hint Extern 100 (spec_refines _ _ _ _ (either _ _ _ _ _ (unfoldMbox ?m))) =>
  either_unfoldMbox m : refines.

Ltac RelGoal_unfoldMbox m :=
  lazymatch m with
  | Mbox_nil =>
    simpl foldMbox; cbn [ Mbox__rec Mbox_rect ] in *;
    unfold SAWCoreScaffolding.fst, SAWCoreScaffolding.snd;
    cbn [ Datatypes.fst Datatypes.snd projT1 ]
  | Mbox_cons _ _ _ _ =>
    simpl foldMbox; cbn [ Mbox__rec Mbox_rect ] in *;
    unfold SAWCoreScaffolding.fst, SAWCoreScaffolding.snd;
    cbn [ Datatypes.fst Datatypes.snd projT1 ]
  | _ => let strt := fresh "strt" in
         let len  := fresh "len" in
         let m0   := fresh "m" in
         let d    := fresh "d" in destruct m as [| strt len m0 d ];
                                  [ RelGoal_unfoldMbox Mbox_nil
                                  | RelGoal_unfoldMbox (Mbox_cons strt len m0 d) ]
  end.

Global Hint Extern 101 (RelGoal (Mbox__rec _ _ _ ?m)) =>
  progress cbn [ Mbox__rec Mbox_rect ] in * : refines.
Global Hint Extern 101 (RelGoal (Mbox_rect _ _ _ ?m)) =>
  progress cbn [ Mbox__rec Mbox_rect ] in * : refines.
Global Hint Extern 101 (RelGoal (Mbox__rec _ _ _ ?m = _)) =>
  progress cbn [ Mbox__rec Mbox_rect ] in * : refines.
Global Hint Extern 101 (RelGoal (Mbox_rect _ _ _ ?m = _)) =>
  progress cbn [ Mbox__rec Mbox_rect ] in * : refines.
Global Hint Extern 101 (RelGoal (_ = Mbox__rec _ _ _ ?m)) =>
  progress cbn [ Mbox__rec Mbox_rect ] in * : refines.
Global Hint Extern 101 (RelGoal (_ = Mbox_rect _ _ _ ?m)) =>
  progress cbn [ Mbox__rec Mbox_rect ] in * : refines.

Global Hint Extern 100 (Shelve (Mbox__rec _ _ _ ?m)) =>
  progress cbn [ Mbox__rec Mbox_rect ] in * : refines.
Global Hint Extern 100 (Shelve (Mbox_rect _ _ _ ?m)) =>
  progress cbn [ Mbox__rec Mbox_rect ] in * : refines.

Lemma IntroArg_eq_Mbox_nil_nil n goal :
  goal -> IntroArg n (Mbox_nil = Mbox_nil) (fun _ => goal).
Proof. do 2 intro; eauto. Qed.

Lemma IntroArg_eq_Mbox_cons_cons n strt1 strt2 len1 len2 m1 m2 d1 d2 goal :
  IntroArg n (strt1 = strt2) (fun _ => IntroArg n (len1 = len2) (fun _ =>
  IntroArg n (m1 = m2) (fun _ => IntroArg n (d1 = d2) (fun _ => goal)))) ->
  IntroArg n (Mbox_cons strt1 len1 m1 d1 = Mbox_cons strt2 len2 m2 d2) (fun _ => goal).
Proof. intros H eq; dependent destruction eq; apply H; eauto. Qed.

Lemma IntroArg_eq_Mbox_nil_cons n strt len m d goal :
  IntroArg n (Mbox_nil = Mbox_cons strt len m d) (fun _ => goal).
Proof. intro eq; dependent destruction eq. Qed.

Lemma IntroArg_eq_Mbox_cons_nil n strt len m d goal :
  IntroArg n (Mbox_cons strt len m d = Mbox_nil) (fun _ => goal).
Proof. intro eq; dependent destruction eq. Qed.

Global Hint Extern 101 (Mbox_nil = Mbox_nil) =>
  simple apply IntroArg_eq_Mbox_nil_nil : refines.
Global Hint Extern 101 (Mbox_cons _ _ _ _ = Mbox_cons _ _ _ _) =>
  simple apply IntroArg_eq_Mbox_cons_cons : refines.
Global Hint Extern 101 (Mbox_nil = Mbox_cons _ _ _ _) =>
  simple apply IntroArg_eq_Mbox_nil_cons : refines.
  Global Hint Extern 101 (Mbox_cons _ _ _ _ = Mbox_nil) =>
    simple apply IntroArg_eq_Mbox_nil_cons : refines.

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

#[local] Hint Rewrite transMbox_Mbox_nil_r (*transMbox_assoc*) : refines.


(* Helper functions and lemmas *)

Definition mbox_chain_length := 
  Mbox_rect (fun _ => nat) O (fun _ _ _ rec _ => S rec).

Lemma mbox_chain_length_transMbox m1 m2 :
  mbox_chain_length (transMbox m1 m2) = mbox_chain_length m1 + mbox_chain_length m2.
Proof. induction m1; simpl; eauto. Qed.


(** * mbox_free_chain *)

Lemma mbox_free_chain_spec_ref m
  : spec_refines eqPreRel eqPostRel eq
      (mbox_free_chain m)
      (total_spec (fun _ => True) (fun _ r => r = intToBv 32 0) (1, m)).
Proof.
  unfold mbox_free_chain, mbox_free_chain__bodies, mboxFreeSpec.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact (a + mbox_chain_length m0).
  - prepost_case 0 0.
    + exact (m0 = m1 /\ a = 1).
    + exact (r = r0).
    prepost_case 1 0.
    + exact (m0 = m1 /\ a = 0).
    + exact (r = r0).
    prepost_exclude_remaining.
  - time "mbox_free_chain_spec_ref" prove_refinement_continue.
Time Qed.


(** * mbox_concat *)

Definition mbox_concat_spec (x y : Mbox) : Mbox :=
  Mbox_rect _ Mbox_nil (fun strt len _ _ d => Mbox_cons strt len y d) x.

Lemma mbox_concat_spec_ref m1 m2
  : spec_refines eqPreRel eqPostRel eq
      (mbox_concat m1 m2)
      (total_spec (fun _ => True)
                  (fun '(m1', m2') r => r = mbox_concat_spec m1' m2')
                  (m1, m2)).
Proof.
  unfold mbox_concat, mbox_concat__bodies.
  prove_refinement.
  - wellfounded_none.
  - prepost_case 0 0.
    + exact (m = m3 /\ m0 = m4).
    + exact (r = r0).
    prepost_exclude_remaining.
  - time "mbox_concat_spec_ref" prove_refinement_continue.
Time Qed.

#[local] Hint Resolve mbox_concat_spec_ref : refines_proofs.


(** * mbox_concat_chains *)

Lemma mbox_rect_identity m :
  Mbox_rect _ Mbox_nil (fun strt len _ rec d => Mbox_cons strt len rec d) m = m.
Proof. induction m; simpl; try f_equal; eauto. Qed. 

Definition mbox_concat_chains_spec (m1 m2 : Mbox) : Mbox :=
  if mbox_chain_length m1 =? 0 then Mbox_nil else transMbox m1 m2.

Lemma mbox_concat_chains_spec_ref__dec_args m1 m2
  : spec_refines eqPreRel eqPostRel eq
      (mbox_concat_chains m1 m2)
      (total_spec (fun _ => True)
                  (fun '(_, m, m1', m2') r => r = mbox_concat_chains_spec (transMbox m m1') m2')
                  (1, Mbox_nil, m1, m2)).
Proof.
  unfold mbox_concat_chains, mbox_concat_chains__bodies, mbox_concat_chains_spec.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact (a + mbox_chain_length m0).
  - prepost_case 0 0.
    + exact (Mbox_nil = m3 /\ m = m4 /\ m0 = m5 /\ a = 1).
    + exact (r = r0).
    prepost_case 1 0.
    + exact (m = m4 /\ Mbox_cons x x0 m3 a = m5 /\ m0 = m6 /\ a0 = 0).
    + exact (r = r0).
    prepost_exclude_remaining.
  - time "mbox_concat_chains_spec_ref__dec_args" prove_refinement_continue.
    + rewrite mbox_chain_length_transMbox, Nat.add_comm; simpl.
      rewrite transMbox_assoc; reflexivity.
    + rewrite transMbox_assoc; reflexivity.
Time Qed.

Lemma mbox_concat_chains_spec_ref__fuel m1 m2
  : spec_refines eqPreRel eqPostRel eq
      (mbox_concat_chains m1 m2)
      (total_spec (fun _ => True)
                  (fun '(_, m1', m2') r => r = mbox_concat_chains_spec m1' m2')
                  (mbox_chain_length m1, m1, m2)).
Proof.
  unfold mbox_concat_chains, mbox_concat_chains__bodies, mbox_concat_chains_spec.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact a.
  - prepost_case 0 0.
    + exact (m = m3 /\ m0 = m4 /\ a = mbox_chain_length m).
    + exact (r = r0).
    prepost_case 1 0.
    + exact (transMbox m (Mbox_cons x x0 m3 a) = m4 /\ m0 = m5 /\
             a0 = mbox_chain_length m3).
    + exact (r = r0).
    prepost_exclude_remaining.
  - time "mbox_concat_chains_spec_ref__fuel" prove_refinement_continue.
    + rewrite mbox_chain_length_transMbox, Nat.add_comm; simpl.
      rewrite transMbox_assoc; reflexivity.
    + rewrite transMbox_assoc; reflexivity.
Time Qed.


(** * mbox_detach *)

Definition mbox_detach_spec : Mbox -> Mbox * Mbox :=
  Mbox_rect _ (Mbox_nil, Mbox_nil)
              (fun strt len next _ d => (next, (Mbox_cons strt len Mbox_nil d))).

Lemma mbox_detach_spec_ref m
  : spec_refines eqPreRel eqPostRel eq
      (mbox_detach m)
      (total_spec (fun _ => True)
                  (fun m r => r = mbox_detach_spec m) m).
Proof.
  unfold mbox_detach, mbox_detach__bodies.
  prove_refinement.
  - wellfounded_none.
  - prepost_case 0 0.
    + exact (m0 = m1).
    + exact (r = r0).
    prepost_exclude_remaining.
  - time "mbox_detach_spec_ref" prove_refinement_continue.
Time Qed.


(** * mbox_drop *)

Definition mbox_drop_spec : Mbox -> bitvector 64 -> Mbox :=
  Mbox_rect _ (fun _ => Mbox_nil) (fun strt len next rec d ix =>
    if bvule 64 len ix
    then Mbox_cons (intToBv 64 0) (intToBv 64 0) (rec (bvSub 64 ix len)) d
    else Mbox_cons (bvAdd 64 strt ix) (bvSub 64 len ix) next d).

Lemma mbox_drop_spec_ref m x
  : spec_refines eqPreRel eqPostRel eq
      (mbox_drop m x)
      (total_spec (fun _ => True)
                  (fun '(m, x) r => r = mbox_drop_spec m x)
                  (m, x)).
Proof.
  unfold mbox_drop, mbox_drop__bodies, mbox_drop_spec.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact (mbox_chain_length m0).
  - prepost_case 0 0.
    + exact (m0 = m1 /\ x0 = x1).
    + exact (r = r0).
    prepost_exclude_remaining.
  - time "mbox_drop_spec_ref" prove_refinement_continue.
    all: cbn [ Mbox_rect ]; rewrite e_if; reflexivity.
Time Qed.


(** * mbox_len *)

Definition mbox_len_spec : Mbox -> bitvector 64 :=
  Mbox__rec (fun _ =>  bitvector 64) (intToBv 64 0)
          (fun strt len m rec d => bvAdd 64 rec len).

Lemma mbox_len_spec_transMbox m1 m2 :
  mbox_len_spec (transMbox m1 m2) =
  bvAdd 64 (mbox_len_spec m1) (mbox_len_spec m2).
Proof.
  induction m1 as [|strt len m1' IH d]; simpl.
  - rewrite bvAdd_id_l.
    reflexivity.
  - rewrite IH.
    rewrite 2 bvAdd_assoc.
    rewrite (bvAdd_comm _ len).
    reflexivity.
Qed.

Lemma mbox_len_spec_ref__dec_args m
  : spec_refines eqPreRel eqPostRel eq
      (mbox_len m)
      (total_spec (fun _ => True)
                  (fun '(_, m1', m2') r => r = (transMbox m1' m2', mbox_len_spec (transMbox m1' m2')))
                  (1, Mbox_nil, m)).
Proof.
  unfold mbox_len, mbox_len__bodies.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact (a + mbox_chain_length m1).
  - prepost_case 0 0.
    + exact (m0 = m2 /\ m1 = Mbox_nil /\ 1 = a).
    + exact (r = r0).
  - prepost_case 1 0.
    + exact (m0 = m2 /\ m1 = m3 /\ 0 = a
              /\ mbox_len_spec m0 = x).
    + exact (r = r0).
    prepost_exclude_remaining.
  - time "mbox_len_spec_ref__dec_args" prove_refinement_continue.
    + rewrite mbox_len_spec_transMbox.
      simpl.
      rewrite bvAdd_id_l.
      reflexivity.
    + rewrite transMbox_assoc.
      reflexivity.
Time Qed.

Lemma mbox_len_spec_ref__fuel m
  : spec_refines eqPreRel eqPostRel eq
      (mbox_len m)
      (total_spec (fun _ => True)
                  (fun '(_, _, m') r => r = (m', mbox_len_spec m'))
                  (1, mbox_chain_length m, m)).
Proof.
  unfold mbox_len, mbox_len__bodies, Mbox_def.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact (a + a0).
  - prepost_case 0 0.
    + exact (m0 = m1 /\ 1 = a /\ mbox_chain_length m0 = a0).
    + exact (r = r0).
  - prepost_case 1 0.
    + exact (transMbox m0 m1 = m2 /\ 0 = a /\ mbox_chain_length m1 = a0
              /\ mbox_len_spec m0 = x).
    + exact (r = r0).
    prepost_exclude_remaining.
  - time "mbox_len_spec_ref__fuel" prove_refinement_continue.
    + rewrite mbox_len_spec_transMbox.
      simpl.
      rewrite bvAdd_id_l.
      reflexivity.
    + rewrite transMbox_assoc.
      reflexivity.
Time Qed.


(** * mbox_copy *)

Definition Mbox_cons_valid (strt len : bitvector 64) : Prop :=
  isBvule 64 strt (intToBv 64 128) /\
  isBvule 64 len (bvSub 64 (intToBv 64 128) strt).

Definition mbox_copy_precond : Mbox -> Prop :=
  Mbox__rec (fun _ => Prop)
            True
            (fun strt len _ _ _ => Mbox_cons_valid strt len).

Definition empty_mbox_d := genBVVec 64 (intToBv 64 128) (bitvector 8) (fun i _ => bvNat 8 0).

(* Return d0, but with the bits in the range [strt, strt+len] replaced with the
   corresponding bits from d1. *)
Definition conjSliceBVVec (strt len : bitvector 64) pf0 pf1 d0 d1 : BVVec 64 bv64_128 (bitvector 8) :=
  updSliceBVVec 64 (intToBv 64 128) _ d0 strt len
    (sliceBVVec 64 (intToBv 64 128) _ strt len pf0 pf1 d1).

Definition mbox_copy_postcond
             (m : Mbox)
             (r : Mbox * Mbox)
           : Prop :=
  Mbox__rec (fun _ => Prop)
            (* If the input Mbox is empty, return an empty Mbox. *)
            (r = (Mbox_nil, Mbox_nil))
            (* If the input Mbox is non-empty, then decompose it into its
               `start`, `len`, and `dat`. Return an mbox chain consisting of
               a single mbox with the given `start` and `len`, and the given
               `dat` with the range 0 to `start` zeroed out. *)
            (fun strt len m' _ d =>
              exists (valid : Mbox_cons_valid strt len),
              match valid with
              | conj pf0 pf1 =>
                  r = (Mbox_cons strt len m'
                                 (conjSliceBVVec strt len pf0 pf1 d d),
                       Mbox_cons strt len Mbox_nil
                                 (conjSliceBVVec strt len pf0 pf1 empty_mbox_d d))
              end)
            m.

Lemma mbox_copy_spec_ref m
  : spec_refines eqPreRel eqPostRel eq
      (mbox_copy m)
      (total_spec (fun m' => mbox_copy_precond m')
                  (fun m' r => mbox_copy_postcond m' r)
                  m).
Proof.
  unfold mbox_copy, mbox_copy__bodies, mboxNewSpec.
  (* Yikes! The below functions may or may not be defined depending on what
     machine compiled mbox.bc *)
  try unfold llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64.
  try unfold llvm__x2eobjectsize__x2ei64__x2ep0i8, __memcpy_chk.
  prove_refinement.
  - wellfounded_none.
  - prepost_case 0 0.
    + exact (m0 = m1).
    + exact (r = r0).
    prepost_exclude_remaining.
  - unfold mbox_copy_precond, mbox_copy_postcond, Mbox_cons_valid,
           empty_mbox_d, conjSliceBVVec in *.
    time "mbox_copy_spec_ref" prove_refinement_continue.
    + rewrite and_bool_eq_false, 2 isBvslt_def_opp in e_if.
      destruct e_if.
      * change (intToBv 64 9223372036854775808) with (bvsmin 64) in H1.
        destruct (not_isBvslt_bvsmin _ _ H1).
      * change (intToBv 64 9223372036854775807) with (bvsmax 64) in H1.
        destruct (not_isBvslt_bvsmax _ _ H1).
    (* All the remaining existential variables don't matter *)
    + Unshelve. all: eauto.
Time Qed.

Definition mbox_copy_spec
           : forall (m : Mbox),
             mbox_copy_precond m -> Mbox :=
  Mbox__rec (fun m' => mbox_copy_precond m' -> Mbox)
            (fun _ => Mbox_nil)
            (fun strt len m' _ d valid =>
              match valid with
              | conj pf0 pf1 =>
                  Mbox_cons strt len Mbox_nil
                            (conjSliceBVVec strt len pf0 pf1 empty_mbox_d d)
              end).

Lemma mbox_copy_spec_ref__alt m
  : spec_refines eqPreRel eqPostRel eq
      (mbox_copy m)
      (total_spec (fun m' => mbox_copy_precond m')
                  (fun m' r => exists (precond : mbox_copy_precond m'),
                               r = (m', mbox_copy_spec m' precond))
                  m).
Proof.
  unfold mbox_copy, mbox_copy__bodies, mboxNewSpec.
  (* Yikes! The below functions may or may not be defined depending on what
     machine compiled mbox.bc *)
  try unfold llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64.
  try unfold llvm__x2eobjectsize__x2ei64__x2ep0i8, __memcpy_chk.
  prove_refinement.
  - wellfounded_none.
  - prepost_case 0 0.
    + exact (m0 = m1).
    + exact (r = r0).
    prepost_exclude_remaining.
  - unfold mbox_copy_precond, mbox_copy_spec, Mbox_cons_valid,
           empty_mbox_d, conjSliceBVVec in *.
    time "mbox_copy_spec_ref__alt" prove_refinement_continue.
    + rewrite updSlice_slice_identity.
      reflexivity.
    + rewrite and_bool_eq_false, 2 isBvslt_def_opp in e_if.
      destruct e_if.
      * change (intToBv 64 9223372036854775808) with (bvsmin 64) in H1.
        destruct (not_isBvslt_bvsmin _ _ H1).
      * change (intToBv 64 9223372036854775807) with (bvsmax 64) in H1.
        destruct (not_isBvslt_bvsmax _ _ H1).
    (* All the remaining existential variables don't matter *)
    Unshelve. all: eauto.
Time Qed.

#[local] Hint Resolve mbox_copy_spec_ref__alt : refines_proofs.


(** * mbox_copy_chain *)

Definition mbox_copy_chain_precond : Mbox -> Prop :=
  Mbox_rect (fun _ => Prop) True (fun strt len _ rec _ =>
    Mbox_cons_valid strt len /\ rec).

(*
(*
Here is the 'naïve' functional translation...
*)

Definition mbox_copy_chain_spec
           : forall (m : Mbox),
             bitvector 64 -> mbox_copy_chain_precond m -> Mbox :=
  Mbox_rect (fun m => bitvector 64 -> mbox_copy_chain_precond m -> Mbox)
            (fun _ _ => Mbox_nil)
            (fun strt len m rec d src_len valid =>
              if bvEq 64 src_len (intToBv 64 0)
                then Mbox_nil
                else
              match valid with
              | conj pf pfrec =>
                let head := mbox_copy_spec (Mbox_cons strt len m d) pf in
                match head with
                | Mbox_nil => Mbox_nil
                | Mbox_cons strt' len' m' d' =>
                  if bvule 64 src_len len'
                    then Mbox_cons strt' src_len m' d'
                    else let rest := rec (bvSub 64 src_len len') pfrec in
                         match rest with
                         | Mbox_nil => head
                         | Mbox_cons _ _ _ _ => mbox_concat_spec head rest
                         end
                end
              end).
*)

(*
And here is a simplified version that evaluates away the calls to
mbox_copy_spec and mbox_concat_spec.
*)
Definition mbox_copy_chain_spec
           : forall (m : Mbox),
             bitvector 64 -> mbox_copy_chain_precond m -> Mbox :=
  Mbox_rect (fun m => bitvector 64 -> mbox_copy_chain_precond m -> Mbox)
            (fun _ _ => Mbox_nil)
            (fun strt len m rec d src_len valid =>
              if bvEq 64 src_len (intToBv 64 0)
                then Mbox_nil
                else
              match valid with
              | conj (conj pf0 pf1) pfrec =>
                let d_copy := conjSliceBVVec strt len pf0 pf1 empty_mbox_d d in
                let head := Mbox_cons strt len Mbox_nil d_copy in
                if bvule 64 src_len len
                  then Mbox_cons strt src_len Mbox_nil d_copy
                  else Mbox_cons strt len (rec (bvSub 64 src_len len) pfrec) d_copy
              end).

Lemma mbox_copy_chain_precond_to_copy_precond :
  forall (m : Mbox),
  mbox_copy_chain_precond m -> mbox_copy_precond m.
Proof.
  intros m copy_chain_precond. destruct m.
  - assumption.
  - destruct copy_chain_precond. assumption.
Qed.

Lemma mbox_copy_chain_len_0
      (m : Mbox)
      (precond : mbox_copy_chain_precond m) :
  mbox_copy_chain_spec m (intToBv 64 0) precond = Mbox_nil.
Proof.
  destruct m; reflexivity.
Qed.

Lemma mbox_copy_chain_spec_ref m src_len
  : spec_refines eqPreRel eqPostRel eq
      (mbox_copy_chain m src_len)
      (total_spec (fun '(m', _) => mbox_copy_chain_precond m')
                  (fun '(m', src_len') r => exists (precond : mbox_copy_chain_precond m'),
                                            r = (m', mbox_copy_chain_spec m' src_len' precond))
                  (m, src_len)).
Proof.
  unfold mbox_copy_chain, mbox_copy_chain__bodies.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact (mbox_chain_length m0).
  - prepost_case 0 0.
    + exact (m0 = m1 /\ x = x0).
    + exact (r = r0).
    prepost_exclude_remaining.
  - unfold mbox_copy_chain_precond, mbox_copy_chain_spec, Mbox_cons_valid.
    time "mbox_copy_chain_spec_ref" prove_refinement_continue.
    + rewrite bvEq_eq in e_if.
      replace x
        with (intToBv 64 0)
        by bvEq_eq.
      rewrite mbox_copy_chain_len_0.
      reflexivity.
    + apply (mbox_copy_chain_precond_to_copy_precond _ H).
    + instantiate (1 := H).
      rewrite transMbox_Mbox_nil_r in H0.
      destruct H0 as [precond e].
      injection e as X Y.
      rewrite X.
      f_equal.
      admit.
    + rewrite transMbox_Mbox_nil_r in H0.
      destruct H0 as [precond e].
      injection e as X Y.
      subst.
      reflexivity.
    + unshelve instantiate (1 := H).
      rewrite transMbox_Mbox_nil_r in H0.
      destruct H0 as [precond e].
      injection e as e1 e2.
      subst.
      destruct H as [[X Y] Z].
      simpl.
      rewrite e_if.
      f_equal. (* Why are there separate len and len0 variables here? *)
      admit.
    + admit.
    + rewrite transMbox_Mbox_nil_r in H0.
      destruct H0 as [precond e].
      injection e as X Y.
      rewrite <- X.
      reflexivity.
    + admit.
    + unshelve instantiate (1 := _).
      { revert H1. revert r0.
        rewrite transMbox_Mbox_nil_r in *.
        intros r0 H1.

        destruct H0, H1.
        injection H0 as X Y.
        rewrite <- X. rewrite <- X in H.
        destruct H.
        split; assumption. }
      admit.
    + admit.
Admitted.


(** * mbox_split_at *)

Definition mbox_split_at_precond : Mbox -> bitvector 64 -> Prop :=
  Mbox_rect (fun _ => bitvector 64 -> Prop)
            (fun _ => True)
            (fun _ len _ rec _ ix =>
              Mbox_cons_valid ix (bvSub 64 len ix) /\ rec (bvSub 64 ix len)).

Definition mbox_split_at_spec :
           forall (m : Mbox) (ix : bitvector 64),
           mbox_split_at_precond m ix -> Mbox * Mbox :=
  Mbox_rect (fun m => forall (ix : bitvector 64), mbox_split_at_precond m ix -> Mbox * Mbox)
            (fun _ _ => (Mbox_nil, Mbox_nil))
            (fun strt len m rec d ix precond =>
              if bvEq 64 ix (intToBv 64 0)
                then (Mbox_nil, Mbox_cons strt len m d)
                else
              if bvEq 64 ix len
                then (Mbox_cons strt len Mbox_nil d, m)
                else
              match precond with
              | conj (conj pf0 pf1) precond_rec =>
                  if bvult 64 len ix
                    then let res := rec (bvSub 64 ix len) precond_rec in
                         (Mbox_cons strt len (fst res) d, snd res)
                    else (Mbox_cons strt ix Mbox_nil d,
                          Mbox_cons (intToBv 64 0) (bvSub 64 len ix) m
                                    (updSliceBVVec 64 bv64_128 _ empty_mbox_d (intToBv 64 0) (bvSub 64 len ix)
                                      (sliceBVVec 64 bv64_128 _ ix (bvSub 64 len ix) pf0 pf1 d)))
              end).

Lemma mbox_split_at_spec_ref m ix
  : spec_refines eqPreRel eqPostRel eq
      (mbox_split_at m ix)
      (total_spec (fun '(m, ix) => mbox_split_at_precond m ix)
                  (fun '(m, ix) r => exists (precond : mbox_split_at_precond m ix),
                                     r = mbox_split_at_spec m ix precond)
                  (m, ix)).
Proof.
  unfold mbox_split_at, mbox_split_at__bodies, mboxNewSpec.
  (* Yikes! The below functions may or may not be defined depending on what
     machine compiled mbox.bc *)
  try unfold llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64.
  try unfold llvm__x2eobjectsize__x2ei64__x2ep0i8, __memcpy_chk.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact (mbox_chain_length m0).
  - prepost_case 0 0.
    + exact (m0 = m1 /\ x = x0).
    + exact (r = r0).
    prepost_exclude_remaining.
  - unfold mbox_split_at_precond, mbox_split_at_spec, Mbox_cons_valid,
           empty_mbox_d, conjSliceBVVec in *.
    time "mbox_split_at_spec_ref" prove_refinement_continue.
    + simpl.
      rewrite e_if.
      reflexivity.
    + simpl.
      rewrite e_if.
      rewrite e_if0.
      reflexivity.
    + simpl.
      rewrite e_if.
      rewrite e_if0.

      unshelve instantiate (1 := _).
      { simpl. split.
        * apply H.
        * revert H1. revert r0.
          rewrite transMbox_Mbox_nil_r.
          intros r0 H1.
          destruct H1 as [precond e].
          apply precond.
      }
      destruct H as [X Y].
      rewrite e_if1.
      reflexivity.
    + revert H1. revert r0.
      rewrite transMbox_Mbox_nil_r.
      intros r0 H1.
      destruct H1 as [precond e].
      rewrite e.
      reflexivity.
    + rewrite bvSub_n_zero in H.
      destruct H0.
      specialize
        (isBvule_bvSub_remove
          _ (bvSub 64 len x)
          (intToBv 64 128)
          x i i0)
        as Hcontra.
      contradiction.
    + destruct H1 as [H0contra H3].
      contradiction.
    + destruct H2 as [H2contra H4].
      contradiction.
    + simpl. split.
      * instantiate (2 := a0).
        instantiate (1 := a1).
        exists (conj (conj a0 a1) H3).
        rewrite e_if.
        rewrite e_if0.
        rewrite e_if1.
        reflexivity.
    + rewrite updSlice_slice_identity.
      reflexivity.
    + rewrite and_bool_eq_false, 2 isBvslt_def_opp in e_if2.
      destruct e_if2.
      * change (intToBv 64 9223372036854775808) with (bvsmin 64) in H1.
        destruct (not_isBvslt_bvsmin _ _ H1).
      * change (intToBv 64 9223372036854775807) with (bvsmax 64) in H1.
        destruct (not_isBvslt_bvsmax _ _ H1).
    (* All the remaining existential variables don't matter *)
    Unshelve.
    all: (simpl; eauto).
    all: try (match goal with
               [H: isBvule 64 ?x (intToBv 64 128) /\ isBvule 64 (bvSub 64 ?len ?x) (bvSub 64 (intToBv 64 128) ?x) |- _] =>
                 (destruct H; assumption)
               end).
Qed.


(** * mbox_randomize *)

Definition mbox_head_len_sub_strt : Mbox -> nat :=
  Mbox_rect (fun _ => nat) 0 (fun strt len _ _ _ =>
    bvToNat 64 (bvSub 64 len strt)).

Definition mbox_randomize_precond : Mbox -> Prop :=
  Mbox_rect (fun _ => Prop) True (fun strt len _ _ _ =>
    (* 0 <= strt <= len < 128 *)
    isBvsle 64 (intToBv 64 0) strt /\ isBvsle 64 strt len /\
    isBvslt 64 len (intToBv 64 128)).

Definition SUCCESS         := intToBv 32 0.
Definition MBOX_NULL_ERROR := intToBv 32 23.

(* - If `m` is non-null, the function returns `SUCCESS` and `m->data` is set to
     some `data'` such that `m->data[i] = data'[i]` for all `i` such that
     `i < m->strt` or `i >= m->len`.
   - Otherwise, the function returns `MBOX_NULL_ERROR`. *)
Definition mbox_randomize_postcond m r : Prop :=
  Mbox__rec (fun _ => Prop)
            (r = (Mbox_nil, MBOX_NULL_ERROR))
            (fun strt len m _ d =>
              exists d', (forall i (pf : isBvult 64 i bv64_128),
                           isBvslt 64 i strt \/ isBvsle 64 len i ->
                           atBVVec _ _ _ d i pf = atBVVec _ _ _ d' i pf)
                         /\ r = (Mbox_cons strt len m d', SUCCESS)) m.

Definition mbox_randomize_invar (strt len i : bitvector 64) : Prop :=
  (* strt <= i <= len *)
  isBvsle 64 strt i /\ isBvsle 64 i len.

Lemma mbox_randomize_spec_ref m
  : spec_refines eqPreRel eqPostRel eq
      (mbox_randomize m)
      (total_spec (fun '(_, m') => mbox_randomize_precond m')
                  (fun '(_, m') r => mbox_randomize_postcond m' r)
                  (1 + mbox_head_len_sub_strt m, m)).
Proof.
  unfold mbox_randomize, mbox_randomize__bodies, randSpec.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact a.
  - prepost_case 0 0.
    + exact (m0 = m1 /\ a = 1 + mbox_head_len_sub_strt m0).
    + exact (r = r0).
    prepost_case 1 0.
    + exact (Mbox_cons x x0 m0 a = m1 /\
             a0 = bvToNat 64 (bvSub 64 x0 x1) /\
             mbox_randomize_invar x x0 x1).
    + exact (r = r0).
    prepost_exclude_remaining.
  - unfold mbox_head_len_sub_strt, mbox_randomize_precond,
           mbox_randomize_postcond, mbox_randomize_invar in *.
    time "mbox_randomize_spec_ref" prove_refinement_continue.
    all: admit.
Admitted.




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
  - destruct a; inversion e_either. destruct e_assuming; assumption.
  - destruct a; inversion e_either. destruct e_assuming as [ Ha1 [ Ha2 Ha3 ]].
    assumption.
  - destruct a; inversion e_either. destruct e_assuming as [ Ha1 [ Ha2 Ha3 ]].
    assumption.
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
  - destruct a; try discriminate. reflexivity.
  - destruct a; inversion e_either.
    destruct e_assuming as [ Ha1 [ Ha2 Ha3 ]]. assumption.
  - destruct a; inversion e_either.
    destruct e_assuming as [ Ha1 [ Ha2 Ha3 ]]. assumption.
  - destruct a; inversion e_either.
    destruct e_assuming as [ Ha1 [ Ha2 Ha3 ]]. assumption.
  - destruct a; inversion e_either. simpl. rewrite transMbox_Mbox_nil_r.
    reflexivity.
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
    else Mbox_cons (bvAdd 64 strt ix) (bvSub 64 len ix) next d).

Lemma mbox_drop_spec_ref
  : refinesFun mbox_drop (fun x ix => returnM (mbox_drop_spec x ix)).
Proof.
  unfold mbox_drop, mbox_drop__tuple_fun, mbox_drop_spec.
  (* Set Ltac Profiling. *)
  time "mbox_drop_spec_ref" prove_refinement.
  (* Show Ltac Profile. Reset Ltac Profile. *)
  - simpl. destruct a; try discriminate e_either. reflexivity.
  - simpl. destruct a; try discriminate e_either.
    inversion e_either. simpl. rewrite <- H0 in e_if. simpl in e_if.
    unfold isBvule in e_if. rewrite e_if. simpl.
    repeat rewrite transMbox_Mbox_nil_r.
    reflexivity.
  - destruct a; simpl in e_either; inversion e_either.
    rewrite <- H0 in e_if. simpl in e_if. simpl.
    assert (bvule 64 v0 a0 = false); [ apply isBvult_def_opp; assumption | ].
    rewrite H. simpl. rewrite transMbox_Mbox_nil_r.
    reflexivity.
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
  - destruct a; simpl in e_either; try discriminate e_either. reflexivity.
  - destruct a; simpl in e_either; inversion e_either.
    rewrite transMbox_Mbox_nil_r. reflexivity.
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
  - destruct a5; simpl in e_either; inversion e_either.
    repeat rewrite transMbox_Mbox_nil_r; reflexivity.
  - destruct a5; simpl in e_either; inversion e_either.
    repeat rewrite transMbox_Mbox_nil_r; reflexivity.
  - destruct a; simpl in e_either; inversion e_either. reflexivity.
  - destruct a; simpl in e_either; inversion e_either.
    destruct a0; simpl in e_either0; inversion e_either0.
    rewrite transMbox_Mbox_nil_r; reflexivity.
  - destruct a; simpl in e_either; inversion e_either.
    destruct a0; simpl in e_either0; inversion e_either0.
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
  - destruct a; simpl in e_either; inversion e_either. reflexivity.
  - destruct a; simpl in e_either; inversion e_either.
    rewrite transMbox_Mbox_nil_r; reflexivity.
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
  all: try rewrite bvAdd_id_r; try rewrite bvAdd_id_l; try reflexivity.
  - destruct a2; simpl in e_either; inversion e_either.
    repeat rewrite transMbox_Mbox_nil_r. rewrite bvAdd_id_r. reflexivity.
  - destruct a2; simpl in e_either; inversion e_either.
    repeat rewrite transMbox_Mbox_nil_r. simpl.
    rewrite bvAdd_assoc. rewrite (bvAdd_comm _ v0). reflexivity.
  - repeat rewrite transMbox_Mbox_nil_r. reflexivity.
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

Lemma eithers2_either {A B C} (f: A -> C) (g: B -> C) e :
  eithers _ (FunsTo_Cons _ _ f (FunsTo_Cons _ _ g (FunsTo_Nil _))) e =
  either _ _ _ f g e.
Proof.
  destruct e; reflexivity.
Qed.

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
  - destruct a; simpl in e_either; inversion e_either. reflexivity.
  - simpl in e_either0. discriminate e_either0.
  - destruct a; simpl in e_either; inversion e_either. simpl.
    apply refinesM_assumingM_r; intro.
    apply refinesM_forallM_r; intro.
    unfold isBvule in a2.
    rewrite <- H0 in e_maybe; simpl in e_maybe.
    rewrite a2 in e_maybe. simpl in e_maybe. discriminate e_maybe.
  - destruct a; simpl in e_either; inversion e_either. simpl.
    apply refinesM_assumingM_r; intro.
    apply refinesM_forallM_r; intro.
    apply refinesM_forallM_r; intro.
    rewrite <- H0 in e_maybe0. simpl in e_maybe0.
    unfold isBvule in a4; rewrite a4 in e_maybe0.
    simpl in e_maybe0. discriminate e_maybe0.
  - destruct a; simpl in e_either; inversion e_either. simpl.
    apply refinesM_assumingM_r; intro.
    apply refinesM_forallM_r; intro.
    apply refinesM_forallM_r; intro.
    rewrite <- H0 in e_maybe1. simpl in e_maybe1.
    unfold isBvule in a4. rewrite a4 in e_maybe1.
    simpl in e_maybe1. discriminate e_maybe1.
  - destruct a; simpl in e_either; inversion e_either. simpl.
    apply refinesM_assumingM_r; intro.
    apply refinesM_forallM_r; intro.
    apply refinesM_forallM_r; intro.
    rewrite <- H0 in e_maybe2. simpl in e_maybe2.
    unfold isBvule in a6. rewrite a6 in e_maybe2.
    simpl in e_maybe2. discriminate e_maybe2.
  - destruct a; simpl in e_either; inversion e_either. simpl.
    prove_refinement with NoRewrite.
    subst a0. simpl. repeat rewrite transMbox_Mbox_nil_r.
    destruct a1; simpl in e_either0; inversion e_either0.
    simpl. unfold conjSliceBVVec.
    replace a4 with e_forall; [ replace a5 with e_forall0;
                                [ reflexivity | ] | ];
    apply BoolDecidableEqDepSet.UIP.
  - elimtype False; apply (not_isBvslt_bvsmin _ _ e_if).
  - elimtype False; apply (not_isBvslt_bvsmax _ _ e_if).
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
