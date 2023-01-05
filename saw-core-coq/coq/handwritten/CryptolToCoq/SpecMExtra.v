(***
 *** Extra Proofs for SpecM that Rely on SAWCorePrelude
 ***)

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.
From EnTree Require Export
     Basics.HeterogeneousRelations
     Basics.QuantType
     Ref.SpecM
     Automation.
Import SAWCorePrelude.


(***
 *** QuantType Instances
 ***)

(** Simple QuantType Instances **)

Program Instance QuantType_Bool : QuantType Bool :=
  { quantEnc := QEnc_nat;
    quantEnum := fun n => match n with
                          | 0 => false
                          | S _ => true
                          end;
    quantEnumInv := fun b => if b then 1 else 0 }.
Next Obligation.
  destruct a; reflexivity.
Defined.


(** QuantType Vec Instance **)

(* Build the encoding of the N-tuple of a given encoding *)
Fixpoint QEnc_NTuple n (qenc : QuantEnc) : QuantEnc :=
  match n with
  | 0 => QEnc_prop True
  | S n' => QEnc_pair qenc (QEnc_NTuple n' qenc)
  end.

(* The quantEnum function for Vec n a *)
Definition quantEnum_Vec n A `{QuantType A} :
  encodes (QEnc_NTuple n (quantEnc (A:=A))) -> Vec n A :=
  nat_rect
    (fun n => encodes (QEnc_NTuple n (quantEnc (A:=A))) -> Vec n A)
    (fun _ => VectorDef.nil _)
    (fun n enumF x => VectorDef.cons _ (quantEnum (fst x)) _ (enumF (snd x)))
    n.

(* The quantEnumInv function for Vec n a *)
Definition quantEnumInv_Vec n A `{QuantType A} :
  Vec n A -> encodes (QEnc_NTuple n (quantEnc (A:=A))) :=
  nat_rect
    (fun n => Vec n A -> encodes (QEnc_NTuple n (quantEnc (A:=A))))
    (fun _ => I)
    (fun n enumInvF x => (quantEnumInv (VectorDef.hd x), enumInvF (VectorDef.tl x)))
    n.

Program Instance QuantType_Vec n A `{QuantType A} : QuantType (Vec n A) :=
  { quantEnc := QEnc_NTuple n (quantEnc (A:=A));
    quantEnum := quantEnum_Vec n A;
    quantEnumInv := quantEnumInv_Vec n A }.
Next Obligation.
  induction a.
  - reflexivity.
  - simpl. rewrite quantEnumSurjective. rewrite IHa. reflexivity.
Defined.

Program Instance QuantType_bitvector w : QuantType (bitvector w) :=
  QuantType_Vec w _.


(***
 *** Additional Automation
 ***)

(* QOL: nicer names for bitvector arguments *)
#[global] Hint Extern 901 (IntroArg Any (bitvector _) _) =>
  let e := fresh "x" in IntroArg_intro e : refines prepostcond.
#[global] Hint Extern 901 (IntroArg RetAny (bitvector _) _) =>
  let e := fresh "r_x" in IntroArg_intro e : refines prepostcond.

(* Maybe automation *)

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


(* Bitvector (In)Equality Automation *)

Lemma simpl_llvm_bool_eq (b : bool) :
  negb (bvEq 1 (if b then intToBv 1 (-1) else intToBv 1 0) (intToBv 1 0)) = b.
Proof. destruct b; eauto. Qed.

Definition simpl_llvm_bool_eq_IntroArg n (b1 b2 : bool) (goal : Prop) :
  IntroArg n (b1 = b2) (fun _ => goal) ->
  IntroArg n (negb (bvEq 1 (if b1 then intToBv 1 (-1) else intToBv 1 0) (intToBv 1 0)) = b2) (fun _ => goal).
Proof. rewrite simpl_llvm_bool_eq; eauto. Defined.

#[global] Hint Extern 101 (IntroArg _ (negb (bvEq 1 (if _ then intToBv 1 (-1) else intToBv 1 0) (intToBv 1 0)) = _) _) =>
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

#[global] Hint Extern 101 (IntroArg _ (bvuleWithProof _ _ _ = Nothing _) _) =>
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

#[global] Hint Extern 101 (IntroArg _ (bvultWithProof _ _ _ = Nothing _) _) =>
  apply bvultWithProof_not_IntroArg : refines.
