From Coq          Require Import Lists.List.
From Coq          Require Import Logic.FunctionalExtensionality.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePreludeExtra.
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


(* Bitvector lemmas *)

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
            _1
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

Lemma isBvult_impl_lt_bvToNat w a b :
  isBvult w a b -> bvToNat w a < bvToNat w b.
Admitted.

Lemma isBvult_bvSub_bvAdd_1 w x y :
  isBvult w y x ->
  isBvult w (bvSub w x (bvAdd w y (intToBv w 1)))
            (bvSub w x y).
Proof. holds_for_bits_up_to_3. Qed.


(* QuantType instance for Mbox *)

Global Instance QuantType_bitvector {w} : QuantType (bitvector w) :=
  { quantEnc := QEnc_nat;
    quantEnum := bvNat w;
    quantEnumInv := bvToNat w;
    quantEnumSurjective := bvNat_bvToNat w }.

Lemma gen_sawAt_eq n a v `{Inhabited a} :
  gen n a (sawAt n a v) = v.
Proof. dependent induction v; simpl; f_equal. apply IHv. Qed.

Program Global Instance QuantType_BVVec_bitvector {w len A}
  `{Inhabited A} `{QuantType A} : QuantType (BVVec w len A) :=
  { quantEnc := QEnc_fun QEnc_nat (quantEnc (A:=A));
    quantEnum := fun f => gen _ _ (fun i => quantEnum (f i));
    quantEnumInv := fun v i => quantEnumInv (sawAt _ _ v i) }.
Next Obligation.
  erewrite <- gen_sawAt_eq with (v := a) at 1.
  apply gen_domain_eq; intro.
  apply quantEnumSurjective.
Qed.

Fixpoint mbox_to_list (m : Mbox) : list (bitvector 64 * bitvector 64 *
                                         BVVec 64 bv64_128 (bitvector 8)) :=
  match m with
  | Mbox_nil => nil
  | Mbox_cons strt len m' d => (strt, len, d) :: mbox_to_list m'
  end.

Fixpoint mbox_from_list (l : list (bitvector 64 * bitvector 64 *
                                   BVVec 64 bv64_128 (bitvector 8))) : Mbox :=
  match l with
  | nil => Mbox_nil
  | (strt, len, d) :: l' => Mbox_cons strt len (mbox_from_list l') d
  end.

Lemma QuantType_Mbox_surjective m :
  mbox_from_list (quantEnum (quantEnumInv (mbox_to_list m))) = m.
Proof.
  rewrite quantEnumSurjective.
  induction m; simpl; f_equal; eauto.
Qed.

Program Global Instance QuantType_Mbox : QuantType Mbox :=
  { quantEnc :=
      quantEnc (A := list (bitvector 64 * bitvector 64 *
                           BVVec 64 bv64_128 (bitvector 8)));
    quantEnum := fun s => mbox_from_list (quantEnum s);
    quantEnumInv := fun m => quantEnumInv (mbox_to_list m);
    quantEnumSurjective := QuantType_Mbox_surjective }.


(* QOL: nicer names for mbox arguments *)
#[local] Hint Extern 901 (IntroArg Any Mbox _) =>
  let e := fresh "m" in IntroArg_intro e : refines prepostcond.
#[local] Hint Extern 901 (IntroArg Any Mbox_def _) =>
  let e := fresh "m" in IntroArg_intro e : refines prepostcond.
#[local] Hint Extern 901 (IntroArg RetAny Mbox _) =>
  let e := fresh "r_m" in IntroArg_intro e : refines prepostcond.
#[local] Hint Extern 901 (IntroArg RetAny Mbox_def _) =>
  let e := fresh "r_m" in IntroArg_intro e : refines prepostcond.


(* Mbox destruction automation *)

Arguments FunsTo_Nil {a}.
Arguments FunsTo_Cons {a tp}.

Lemma spec_refines_either_unfoldMbox_nil_l (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) f g (P : SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR (f tt) P ->
  spec_refines RPre RPost RR (eithers _ (FunsTo_Cons f (FunsTo_Cons g FunsTo_Nil))
                                        (unfoldMbox Mbox_nil)) P.
Proof. eauto. Qed.

Lemma spec_refines_either_unfoldMbox_cons_l (E1 E2 : EvType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) strt len m d f g (P : SpecM E2 Γ2 R2) :
  spec_refines RPre RPost RR (g (strt, (len, (m, d)))) P ->
  spec_refines RPre RPost RR (eithers _ (FunsTo_Cons f (FunsTo_Cons g FunsTo_Nil))
                                        (unfoldMbox (Mbox_cons strt len m d))) P.
Proof. eauto. Qed.

Ltac eithers_unfoldMbox m :=
  let m' := eval cbn [ fst snd projT1 ] in m in
  lazymatch m' with
  | Mbox_nil =>
    simple apply spec_refines_either_unfoldMbox_nil_l
  | Mbox_cons ?strt ?len ?m0 ?d =>
    simple apply (spec_refines_either_unfoldMbox_cons_l _ _ _ _ _ _ _ _ _ strt len m0 d)
  | _ => let strt := fresh "strt" in
         let len  := fresh "len" in
         let m0   := fresh "m" in
         let d    := fresh "d" in
         let eq   := fresh "e_destruct" in
         destruct m' as [| strt len m0 d ] eqn:eq;
         [ eithers_unfoldMbox Mbox_nil
         | eithers_unfoldMbox (Mbox_cons strt len m0 d) ];
         simpl foldMbox; cbn [ Mbox__rec Mbox_rect ] in *;
         cbn [ fst snd projT1 ];
         revert eq; apply (IntroArg_fold Destruct)
  end.

Global Hint Extern 100 (spec_refines _ _ _ (eithers _ _ (unfoldMbox ?m)) _) =>
  eithers_unfoldMbox m : refines.
Global Hint Extern 100 (spec_refines _ _ _ _ (eithers _ _ (unfoldMbox ?m))) =>
  eithers_unfoldMbox m : refines.

Global Hint Extern 901 (RelGoal _) =>
  progress (simpl foldMbox in *; cbn [ Mbox__rec Mbox_rect ] in *) : refines.

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

#[local] Hint Rewrite transMbox_Mbox_nil_r transMbox_assoc : refines.


(* Helper functions and lemmas *)

Tactic Notation "rewrite_transMbox_Mbox_nil_r_dep" "in" ident(H1) :=
  revert H1; rewrite transMbox_Mbox_nil_r; intros H1.
Tactic Notation "rewrite_transMbox_Mbox_nil_r_dep" "in" ident(H1) ident(H2) :=
  revert H1 H2; rewrite transMbox_Mbox_nil_r; intros H1 H2.
Tactic Notation "rewrite_transMbox_Mbox_nil_r_dep" "in" ident(H1) ident(H2) ident(H3) :=
  revert H1 H2 H3; rewrite transMbox_Mbox_nil_r; intros H1 H2 H3.

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
    + exact (r_m = r_m0).
    prepost_exclude_remaining.
  - time "mbox_concat_spec_ref" prove_refinement_continue.
Time Qed.

#[local] Hint Resolve mbox_concat_spec_ref : refines_proofs.


(** * mbox_concat_chains (two proofs) *)

Lemma mbox_rect_identity m :
  Mbox_rect _ Mbox_nil (fun strt len _ rec d => Mbox_cons strt len rec d) m = m.
Proof. induction m; simpl; try f_equal; eauto. Qed.

Definition mbox_concat_chains_spec (m1 m2 : Mbox) : Mbox :=
  if mbox_chain_length m1 =? 0 then Mbox_nil else transMbox m1 m2.

(* Proof 1: A version where the arguments to total_spec match the recursive
   structure of the function: with one argument keeping track of the Mbox
   blocks seen, and the other keeping track of the blocks yet to be seen.
   Thus, the decreasing nat is just the length of this second Mbox. *)
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
    + exact (r_m = r_m0).
    prepost_case 1 0.
    + exact (m = m4 /\ Mbox_cons x x0 m3 a = m5 /\ m0 = m6 /\ a0 = 0).
    + exact (r_m = r_m0).
    prepost_exclude_remaining.
  - time "mbox_concat_chains_spec_ref__dec_args" prove_refinement_continue.
    + rewrite mbox_chain_length_transMbox, Nat.add_comm.
      reflexivity.
Time Qed.

(* Proof 2: A version where one argument to total_spec is designated as the
   'fuel' - in this case starting at mbox_chain_length m1 and decreasing
   each call - but the actual Mbox argument (m1) stays constant. *)
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
    + exact (r_m = r_m0).
    prepost_case 1 0.
    + exact (transMbox m (Mbox_cons x x0 m3 a) = m4 /\ m0 = m5 /\
             a0 = mbox_chain_length m3).
    + exact (r_m = r_m0).
    prepost_exclude_remaining.
  - time "mbox_concat_chains_spec_ref__fuel" prove_refinement_continue.
    + rewrite mbox_chain_length_transMbox, Nat.add_comm.
      reflexivity.
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
    + exact (r_m = r_m1 /\ r_m0 = r_m2).
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
    + exact (r_m = r_m0).
    prepost_exclude_remaining.
  - time "mbox_drop_spec_ref" prove_refinement_continue.
    all: rewrite e_if; reflexivity.
Time Qed.


(** * mbox_len (two proofs) *)

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

(* Proof 1: A version where the arguments to total_spec match the recursive
   structure of the function: with one argument keeping track of the Mbox
   blocks seen, and the other keeping track of the blocks yet to be seen.
   Thus, the decreasing nat is just the length of this second Mbox. *)
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
    + exact (r_m = r_m0 /\ r_x = r_x0).
  - prepost_case 1 0.
    + exact (m0 = m2 /\ m1 = m3 /\ 0 = a
              /\ mbox_len_spec m0 = x).
    + exact (r_m = r_m0 /\ r_x = r_x0).
    prepost_exclude_remaining.
  - time "mbox_len_spec_ref__dec_args" prove_refinement_continue.
    + rewrite mbox_len_spec_transMbox.
      simpl.
      rewrite bvAdd_id_l.
      reflexivity.
Time Qed.

(* Proof 1: A version where one argument to total_spec is designated as the
   'fuel' - in this case starting at mbox_chain_length m and decreasing
   each call - but the actual Mbox argument (m) stays constant. *)
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
    + exact (r_m = r_m0 /\ r_x = r_x0).
  - prepost_case 1 0.
    + exact (transMbox m0 m1 = m2 /\ 0 = a /\ mbox_chain_length m1 = a0
              /\ mbox_len_spec m0 = x).
    + exact (r_m = r_m0 /\ r_x = r_x0).
    prepost_exclude_remaining.
  - time "mbox_len_spec_ref__fuel" prove_refinement_continue.
    + rewrite mbox_len_spec_transMbox.
      simpl.
      rewrite bvAdd_id_l.
      reflexivity.
Time Qed.

#[local] Hint Resolve mbox_len_spec_ref__fuel : refines_proofs.


(** * mbox_copy *)

Definition Mbox_cons_valid (strt len : bitvector 64) : Prop :=
  isBvule 64 strt (intToBv 64 128) /\
  isBvule 64 len (bvSub 64 (intToBv 64 128) strt).

Lemma Mbox_cons_valid_proof_irrel
        (strt len : bitvector 64)
        (p1 p2 : Mbox_cons_valid strt len) :
  p1 = p2.
Proof.
  destruct p1 as [X1 Y1], p2 as [X2 Y2].
  f_equal; apply UIP_bool.
Qed.

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

Lemma mbox_copy_nil (m : Mbox) (precond : mbox_copy_precond m) :
  mbox_copy_spec m precond = Mbox_nil ->
  m = Mbox_nil.
Proof.
  destruct m, precond; simpl.
  - reflexivity.
  - discriminate.
Qed.

Lemma mbox_copy_spec_ref m
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
    + exact (r_m = r_m1 /\ r_m0 = r_m2).
    prepost_exclude_remaining.
  - unfold mbox_copy_precond, mbox_copy_spec, Mbox_cons_valid,
           empty_mbox_d, conjSliceBVVec in *.
    time "mbox_copy_spec_ref" prove_refinement_continue.
    + rewrite updSlice_slice_identity.
      reflexivity.
    + rewrite and_bool_eq_false, 2 isBvslt_def_opp in e_if.
      destruct e_if.
      * change (intToBv 64 9223372036854775808) with (bvsmin 64) in H.
        destruct (not_isBvslt_bvsmin _ _ H).
      * change (intToBv 64 9223372036854775807) with (bvsmax 64) in H.
        destruct (not_isBvslt_bvsmax _ _ H).
    (* All the remaining existential variables don't matter *)
    Unshelve. all: eauto.
Time Qed.

#[local] Hint Resolve mbox_copy_spec_ref : refines_proofs.


(** * mbox_copy_chain *)

Definition mbox_copy_chain_precond : Mbox -> Prop :=
  Mbox_rect (fun _ => Prop) True (fun strt len _ rec _ =>
    Mbox_cons_valid strt len /\ rec).

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

Lemma mbox_copy_chain_precond_proof_irrel
        (m : Mbox)
        (p1 p2 : mbox_copy_chain_precond m) :
  p1 = p2.
Proof.
  induction m.
  - destruct p1, p2. reflexivity.
  - destruct p1 as [X1 Y1], p2 as [X2 Y2].
    f_equal.
    + apply Mbox_cons_valid_proof_irrel.
    + apply IHm.
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
    + exact (r_m = r_m1 /\ r_m0 = r_m2).
    prepost_exclude_remaining.
  - unfold mbox_copy_chain_precond, mbox_copy_chain_spec, Mbox_cons_valid.
    time "mbox_copy_chain_spec_ref" prove_refinement_continue.
    + rewrite bvEq_eq in e_if.
      replace x
        with (intToBv 64 0)
        by bvEq_eq.
      rewrite mbox_copy_chain_len_0.
      reflexivity.
    + apply (mbox_copy_chain_precond_to_copy_precond _ e_assume).
    + rewrite_transMbox_Mbox_nil_r_dep in a e_destruct.
      apply mbox_copy_nil in e_destruct.
      subst m0.
      reflexivity.
    + rewrite transMbox_Mbox_nil_r in e_destruct0.
      symmetry. assumption.
    + rewrite transMbox_Mbox_nil_r in e_destruct0.
      subst m0.
      reflexivity.
    + rewrite transMbox_Mbox_nil_r in e_destruct0.
      symmetry. assumption.
    + rewrite_transMbox_Mbox_nil_r_dep in a e_destruct e_destruct0.
      instantiate (1 := e_assume).
      subst m0.
      destruct a as [pf0 pf1].
      destruct e_assume as [[X Y] Z].
      simpl in e_destruct.
      injection e_destruct as h1 h2 h3 h4.
      subst strt len m1 d.
      simpl.
      rewrite e_if.
      rewrite e_if0.
      replace pf0 with X by (apply UIP_bool).
      replace pf1 with Y by (apply UIP_bool).
      reflexivity.
    + rewrite transMbox_Mbox_nil_r in e_destruct0.
      subst m0.
      destruct e_assume as [XY Z].
      apply Z.
    + rewrite transMbox_Mbox_nil_r in e_destruct0.
      subst m0.
      reflexivity.
    + rewrite transMbox_Mbox_nil_r in e_destruct0.
      subst m0.
      destruct e_assume as [XY Z].
      apply Z.
    + rewrite transMbox_Mbox_nil_r in e_destruct0.
      subst m0.
      destruct H as [precond e].
      injection e as e1 e2.
      rewrite transMbox_Mbox_nil_r in e1.
      subst r_m1.
      reflexivity.
    + rewrite_transMbox_Mbox_nil_r_dep in a e_destruct.
      rewrite transMbox_Mbox_nil_r in *.
      instantiate (1 := e_assume).
      subst m0.
      destruct a as [pf0 pf1].
      destruct e_assume as [[X Y] Z].
      simpl in e_destruct.
      injection e_destruct as h1 h2 h3 h4.
      subst strt len m1 d.
      simpl.
      rewrite e_if.
      rewrite e_if0.
      destruct H as [precond e].
      injection e as e1 e2.
      replace Z
        with precond
        by (apply mbox_copy_chain_precond_proof_irrel).
      rewrite <- e2.
      replace pf0 with X by (apply UIP_bool).
      replace pf1 with Y by (apply UIP_bool).
      reflexivity.
    + rewrite transMbox_Mbox_nil_r in *.
      subst m0.
      destruct H as [precond e].
      injection e as e1 e2.
      subst r_m1.
      reflexivity.
    + rewrite_transMbox_Mbox_nil_r_dep in a e_destruct.
      rewrite transMbox_Mbox_nil_r in *.
      instantiate (1 := e_assume).
      subst m0.
      destruct a as [pf0 pf1].
      destruct e_assume as [[X Y] Z].
      simpl in e_destruct.
      injection e_destruct as h1 h2 h3 h4.
      subst strt len m1 d.
      simpl.
      rewrite e_if.
      rewrite e_if0.
      destruct H as [precond e].
      injection e as e1 e2.
      replace Z
        with precond
        by (apply mbox_copy_chain_precond_proof_irrel).
      rewrite <- e2.
      replace pf0 with X by (apply UIP_bool).
      replace pf1 with Y by (apply UIP_bool).
      reflexivity.
    (* All the remaining existential variables don't matter *)
    Unshelve. all: eauto.
Qed.

#[local] Hint Resolve mbox_copy_chain_spec_ref : refines_proofs.


(** * mbox_split_at *)

Definition mbox_split_at_precond : Mbox -> bitvector 64 -> Prop :=
  Mbox_rect (fun _ => bitvector 64 -> Prop)
            (fun _ => True)
            (fun _ len _ rec _ ix =>
              Mbox_cons_valid ix (bvSub 64 len ix) /\ rec (bvSub 64 ix len)).

Lemma mbox_split_at_precond_proof_irrel :
  forall (m : Mbox)
         (ix : bitvector 64)
         (p1 p2 : mbox_split_at_precond m ix),
  p1 = p2.
Proof.
  intros m. induction m; intros ix p1 p2.
  - destruct p1, p2. reflexivity.
  - destruct p1 as [X1 Y1], p2 as [X2 Y2].
    f_equal.
    + apply Mbox_cons_valid_proof_irrel.
    + apply IHm.
Qed.

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
                          Mbox_cons (bvNat 64 0) (bvSub 64 len ix) m
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
    + exact (r_m = r_m1 /\ r_m0 = r_m2).
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
      { split; assumption. }
      destruct e_assume as [X Y].
      rewrite e_if1.
      reflexivity.
    + rewrite_transMbox_Mbox_nil_r_dep in r_m1 r_m2 H.
      destruct H as [precond e].
      replace e_assume0
        with precond
        by (apply mbox_split_at_precond_proof_irrel).
      apply (f_equal fst) in e.
      simpl in e.
      subst r_m1.
      reflexivity.
    + rewrite_transMbox_Mbox_nil_r_dep in r_m1 r_m2 H.
      destruct H as [precond e].
      replace e_assume0
        with precond
        by (apply mbox_split_at_precond_proof_irrel).
      apply (f_equal snd) in e.
      simpl in e.
      assumption.
    + rewrite bvSub_n_zero in H.
      destruct e_assume.
      specialize
        (isBvule_bvSub_remove
          _ (bvSub 64 len x)
          (intToBv 64 128)
          x i i0)
        as Hcontra.
      contradiction.
    + destruct e_assume as [H0contra H3].
      contradiction.
    + destruct e_assume as [H2contra H4].
      contradiction.
    + rewrite e_if.
      rewrite e_if0.
      rewrite e_if1.
      unshelve instantiate (1 := _).
      { split; assumption. }
      instantiate (2 := a0).
      instantiate (1 := a1).
      destruct e_assume as [X Y].
      replace a0 with X by (apply UIP_bool).
      replace a1 with Y by (apply UIP_bool).
      reflexivity.
    + rewrite updSlice_slice_identity.
      split; reflexivity.
    + rewrite and_bool_eq_false, 2 isBvslt_def_opp in e_if2.
      destruct e_if2.
      * change (intToBv 64 9223372036854775808) with (bvsmin 64) in H.
        destruct (not_isBvslt_bvsmin _ _ H).
      * change (intToBv 64 9223372036854775807) with (bvsmax 64) in H.
        destruct (not_isBvslt_bvsmax _ _ H).
    (* All the remaining existential variables don't matter *)
    Unshelve. all: (try destruct e_assume; simpl; eauto).
Qed.

#[local] Hint Resolve mbox_split_at_spec_ref : refines_proofs.


(** * mbox_detach_from_end *)

Definition mbox_detach_from_end_precond
             (m : Mbox)
             (length_from_end : bitvector 64)
         : Prop :=
  mbox_split_at_precond m (bvSub 64 (mbox_len_spec m) length_from_end).

Definition mbox_detach_from_end_spec
             (m : Mbox)
             (length_from_end : bitvector 64)
             (precond : mbox_detach_from_end_precond m length_from_end)
         : Mbox * Mbox :=
  mbox_split_at_spec m (bvSub 64 (mbox_len_spec m) length_from_end) precond.

Lemma mbox_detach_from_end_spec_ref m length_from_end
  : spec_refines eqPreRel eqPostRel eq
      (mbox_detach_from_end m length_from_end)
      (total_spec (fun '(m', length_from_end') =>
                    mbox_detach_from_end_precond m' length_from_end')
                  (fun '(m', length_from_end') r =>
                    exists (precond : mbox_detach_from_end_precond m' length_from_end'),
                    r = mbox_detach_from_end_spec m' length_from_end' precond)
                  (m, length_from_end)).
Proof.
  unfold mbox_detach_from_end, mbox_detach_from_end__bodies.
  prove_refinement.
  - wellfounded_none.
  - prepost_case 0 0.
    + exact (m0 = m1 /\ x = x0).
    + exact (r_m = r_m1 /\ r_m0 = r_m2).
    prepost_exclude_remaining.
  - unfold mbox_detach_from_end_precond, mbox_detach_from_end_spec.
  - time "mbox_detach_from_end_spec_ref" prove_refinement_continue.
    Ltac busywork a e_assert := simpl in *;
      repeat rewrite_transMbox_Mbox_nil_r_dep in a e_assert.
    + unshelve instantiate (1 := _).
      { busywork a e_assert. apply a. }
      busywork a e_assert.
      rewrite -> e_assert.
      reflexivity.
    + unshelve instantiate (1 := _).
      { busywork a e_assert. apply a. }
      busywork a e_assert.
      rewrite -> e_assert.
      reflexivity.
Qed.


(** * mbox_randomize *)

Lemma atBVVec_upd_out_of_range w len A a v i j pf :
  bvEq w i j = false ->
  atBVVec w len A v i pf =
  atBVVec w len A (updBVVec w len A v j a) i pf.
Proof.
  intros. unfold updBVVec.
  rewrite at_gen_BVVec.
  rewrite H. reflexivity.
Qed.

(* True iff both inputs are Mbox_null, or both inputs are
   Mbox_cons where the values of strt, len, and m are equal,
   and the values of d are equal only outside of the range
   defined by strt and len. *)
Definition mbox_eq_up_to_head_data (m1 m2 : Mbox) : Prop :=
  Mbox__rec (fun _ => Prop)
            (Mbox__rec (fun _ => Prop) True (fun _ _ _ _ _ => False) m2)
            (fun strt1 len1 m1 _ d1 =>
             Mbox__rec (fun _ => Prop) False (fun strt2 len2 m2 _ d2 =>
             strt1 = strt2 /\ len1 = len2 /\ m1 = m2 /\
             forall i (pf : isBvult 64 i bv64_128),
               isBvslt 64 i strt1 \/ isBvsle 64 len1 i ->
               atBVVec _ _ _ d1 i pf = atBVVec _ _ _ d2 i pf) m2) m1.

Lemma mbox_eq_up_to_head_data_trans m1 m2 m3 :
  mbox_eq_up_to_head_data m1 m2 ->
  mbox_eq_up_to_head_data m2 m3 ->
  mbox_eq_up_to_head_data m1 m3.
Proof.
  destruct m1 as [|strt1 len1 m1 d1],
           m2 as [|strt2 len2 m2 d2],
           m3 as [|strt3 len3 m3 d3]; simpl.
  all: intros; contradiction || eauto.
  destruct H as [? [? []]], H0 as [? [? []]]; repeat split; eauto.
  - transitivity strt2; eauto.
  - transitivity len2; eauto.
  - transitivity m2; eauto.
  - intros. transitivity (atBVVec 64 bv64_128 (bitvector 8) d2 i pf).
    + apply H3. eauto.
    + apply H6. destruct H, H1. eauto.
Qed.

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

Definition mbox_randomize_ret m :=
  Mbox__rec (fun _ => bitvector 32) MBOX_NULL_ERROR
            (fun _ _ _ _ _ => SUCCESS) m.

Definition mbox_randomize_invar (strt len i : bitvector 64) : Prop :=
  (* strt <= i <= len *)
  isBvsle 64 strt i /\ isBvsle 64 i len.

Lemma mbox_randomize_spec_ref m
  : spec_refines eqPreRel eqPostRel eq
      (mbox_randomize m)
      (total_spec (fun '(_, m') => mbox_randomize_precond m')
                  (fun '(_, m') '(r_m, r_x) => mbox_eq_up_to_head_data m' r_m
                                               /\ r_x = mbox_randomize_ret m')
                  (1 + mbox_head_len_sub_strt m, m)).
Proof.
  unfold mbox_randomize, mbox_randomize__bodies, randSpec.
  prove_refinement.
  - wellfounded_decreasing_nat.
    exact a.
  - prepost_case 0 0.
    + exact (m0 = m1 /\ a = 1 + mbox_head_len_sub_strt m0).
    + exact (r_m = r_m0 /\ r_x = r_x0).
    prepost_case 1 0.
    + exact (Mbox_cons x x0 m0 a = m1 /\
             a0 = bvToNat 64 (bvSub 64 x0 x1) /\
             mbox_randomize_invar x x0 x1).
    + exact (r_m = r_m0 /\ r_x = r_x0).
    prepost_exclude_remaining.
  - unfold mbox_head_len_sub_strt, mbox_randomize_precond,
           mbox_randomize_invar in *.
    time "mbox_randomize_spec_ref" prove_refinement_continue.
    (* mbox_eq_up_to_head_data goals *)
    1-3: rewrite transMbox_Mbox_nil_r in H.
    1-3: destruct H.
    1-3: assumption.
    (* Showing the error case of the array bounds check is impossible by virtue *)
    (* of our loop invariant *)
    1-2: enough (isBvult 64 call3 (intToBv 64 128)) by contradiction.
    1-2: destruct e_assume as [?e_assume [?e_assume ?e_assume]].
    1-2: rewrite isBvult_def in e_if; rewrite e_if.
    1-2: eapply isBvult_to_isBvslt_pos; [| reflexivity | assumption ].
    1-2: rewrite e_assume, e_assume0; reflexivity.
    (* Showing the loop invariant holds inductively *)
    1-9: destruct e_assume as [?e_assume [?e_assume ?e_assume]]; try assumption.
    + apply isBvult_impl_lt_bvToNat, isBvult_bvSub_bvAdd_1; eauto.
    + rewrite H. apply isBvsle_suc_r.
      rewrite H0, e_assume1.
      reflexivity.
    + apply isBvslt_to_isBvsle_suc.
      apply isBvult_to_isBvslt_pos; eauto.
      * rewrite e_assume; eauto.
      * rewrite <- e_assume0; eauto.
    (* more step mbox_eq_up_to_head_data goals *)
    1-3: rewrite transMbox_Mbox_nil_r in H2.
    1-3: destruct H2.
    1-2: destruct e_assume as [?e_assume [?e_assume ?e_assume]].
    1-2: rewrite H in e_assume.
    1-2: rewrite isBvult_def in e_if.
    1-2: apply isBvult_to_isBvslt_pos in e_if;
         [| assumption | rewrite <- H0; assumption ].
    1-2: eapply mbox_eq_up_to_head_data_trans; eauto.
    1-2: repeat split; eauto; intros.
    1-2: apply atBVVec_upd_out_of_range.
    1-2: destruct H4 as [?H | ?H]; [| rewrite bvEq_sym ].
    1-4: apply isBvslt_to_bvEq_false.
    + rewrite <- H; assumption.
    + rewrite H4 in e_if; assumption.
    + rewrite <- H; assumption.
    + rewrite H4 in e_if; assumption.
    + rewrite H3. simpl. reflexivity.
    (* Showing the error case of the overflow check is impossible by virtue of *)
    (* our loop invariant *)
    1-2: destruct e_assume as [?e_assume [?e_assume ?e_assume]].
    1-2: rewrite H in e_assume; rewrite <- H0 in e_assume1.
    1-2: rewrite and_bool_eq_false in e_if0.
    1-2: do 2 rewrite isBvslt_def_opp in e_if0.
    1-2: destruct e_if0 as [?e_if | ?e_if];
         [ rewrite <- e_assume in e_if0 | rewrite e_assume1 in e_if0 ].
    1-4: vm_compute in e_if0; discriminate e_if0.
    (* final mbox_eq_up_to_head_data goals *)
    + simpl. repeat split.
    + simpl. repeat split.
    (* All the remaining existential variables don't matter *)
    Unshelve. all: eauto.
Qed.
