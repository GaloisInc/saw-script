(***
 *** A version of the computation monad using the option-set monad
 ***)

From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts.
From Paco Require Import paco.

Infix ">>=" := ITree.bind (at level 58, left associativity).
Notation "m1 >> m2" := (m1 >>= fun _ => m2) (at level 58, left associativity).


(** * `itree_spec` **)

Variant SpecEvent (E:Type -> Type) (A:Type) : Type :=
| Spec_vis : E A -> SpecEvent E A
| Spec_forall : SpecEvent E A
| Spec_exists : SpecEvent E A
.

Arguments Spec_vis {E A}.
Arguments Spec_forall {E A}.
Arguments Spec_exists {E A}.

(* An ITree that defines a set of ITrees *)
Notation itree_spec E := (itree (SpecEvent E)).

(* The body of an itree_spec, inside the observe projection *)
Notation itree_spec' E A := (itree' (SpecEvent E) A).


(** * `satisfies` **)

Inductive satisfiesF {E A} (satisfies : itree_spec E A -> itree E A -> Prop)
  : itree_spec' E A -> itree' E A -> Prop :=
| Satisfies_Ret a : satisfiesF satisfies (RetF a) (RetF a)
| Satisfies_Tau spec tree :
    satisfies spec tree ->
    satisfiesF satisfies (TauF spec) (TauF tree)
| Satisfies_TauL spec tree :
    satisfiesF satisfies (observe spec) tree ->
    satisfiesF satisfies (TauF spec) tree
| Satisfies_TauR spec tree :
    satisfiesF satisfies spec (observe tree) ->
    satisfiesF satisfies spec (TauF tree)
| Satisfies_Vis X (e:E X) spec tree :
    (forall x, satisfies (spec x) (tree x)) ->
    satisfiesF satisfies (VisF (Spec_vis e) spec) (VisF e tree)
| Satisfies_Forall X spec tree :
    (forall x:X, satisfies (spec x) tree) ->
    satisfiesF satisfies (VisF Spec_forall spec) (observe tree)
| Satisfies_Exists X spec tree :
    (exists x:X, satisfies (spec x) tree) ->
    satisfiesF satisfies (VisF Spec_exists spec) (observe tree)
.

Hint Constructors satisfiesF : core.

Instance Proper_satisfies_satisfiesF {E A} :
  Proper (pointwise_relation _ (pointwise_relation _ Basics.impl) ==>
          eq ==> eq ==> Basics.impl) (@satisfiesF E A).
Proof.
  intros R1 R2 implR spec1 spec2 e_spec tree1 tree2 e_tree sats.
  rewrite <- e_spec; rewrite <- e_tree.
  clear e_spec spec2 e_tree tree2.
  induction sats; constructor; intros; try (apply implR; apply H); try assumption.
  destruct H as [ x H ]. exists x. apply implR; assumption.
Qed.

Lemma satisfiesF_mono {E A} (sats1 sats2:itree_spec E A -> itree E A -> Prop)
         (sub_sats:forall spec tree, sats1 spec tree -> sats2 spec tree) :
  forall spec tree,
    satisfiesF sats1 spec tree -> satisfiesF sats2 spec tree.
Proof.
  intros.
  apply (Proper_satisfies_satisfiesF sats1 sats2 sub_sats _ _ eq_refl _ _ eq_refl H).
Qed.

Definition satisfies_ {E A} satisfies spec tree :=
  @satisfiesF E A satisfies (observe spec) (observe tree).

Lemma satisfies__mono E A : monotone2 (@satisfies_ E A).
Proof.
  intros spec tree r1 r2 sats sub12. unfold satisfies_.
  induction sats; constructor; try assumption.
  { apply sub12; assumption. }
  { intros; apply sub12. apply H. }
  { intros; apply sub12. apply H. }
  { destruct H as [ x H ]. exists x. apply sub12. apply H. }
Qed.

Hint Resolve satisfies__mono : paco.

Definition satisfies {E A} spec tree := paco2 (@satisfies_ E A) bot2 spec tree.

Instance Proper_observing_paco2_satisfies_impl E A r :
  Proper (observing eq ==> observing eq ==> iff) (paco2 (@satisfies_ E A) r).
Proof.
  intros spec1 spec2 [ Rspec ] tree1 tree2 [ Rtree ].
  split; intro; punfold H; pfold; unfold satisfies_;
    [ rewrite <- Rtree; rewrite <- Rspec | rewrite Rtree; rewrite Rspec ];
    apply H.
Qed.

Instance Proper_observing_satisfies E A :
  Proper (observing eq ==> observing eq ==> iff) (@satisfies E A).
Proof.
  apply Proper_observing_paco2_satisfies_impl.
Qed.


(** * `satisfies` is proper wrt `eutt` **)

Ltac simpobs x := apply simpobs in x.

Ltac weaken_bis Hb := match type of Hb with ?x ≅ ?y => assert (x ≈ y); try (rewrite Hb; reflexivity) end.

Lemma satisfies_eutt_spec_tau_vis_aux: forall (E : Type -> Type) (A u : Type) (e : SpecEvent E u)
                                         (k1 k2 : u -> itree (SpecEvent E) A),
    (forall v : u, paco2 (eqit_ eq true true id) bot2 (k1 v) (k2 v)) ->
    forall (r : itree_spec E A -> itree E A -> Prop) (tree0 : itree E A),
      (forall (P1 P2 : itree_spec E A) (tree : itree E A),
          satisfies P1 tree -> P1 ≈ P2 -> r P2 tree) ->
      satisfiesF (upaco2 satisfies_ bot2) (VisF e k1) (observe tree0) ->
      satisfiesF (upaco2 satisfies_ r) (VisF e k2) (observe tree0).
Proof.
  intros E A u e k1 k2 REL r tree0 CIH H.
  dependent induction H.
  - rewrite <- x. constructor. eapply IHsatisfiesF; eauto.
  - rewrite <- x. constructor. intros. right.
    pclearbot. eapply CIH; eauto. apply H.
  - rewrite <- x. constructor. right. pclearbot; eapply CIH; eauto.
    apply H.
  - rewrite <- x. constructor. destruct H as [x' Hx' ]. pclearbot.
    exists x'. right. eapply CIH; eauto.
Qed.

Lemma satisfiesF_TauL: forall (E : Type -> Type) (A : Type) (t1 : itree (SpecEvent E) A)
                         (tree0 : itree E A),
    satisfiesF (upaco2 satisfies_ bot2) (TauF t1) (observe tree0) ->
    satisfiesF (upaco2 satisfies_ bot2) (observe t1) (observe tree0).
Proof.
  intros E A t1 tree0 H.
  dependent induction H; auto.
  - pclearbot. rewrite <- x. constructor. punfold H.
  - rewrite <- x. constructor. eapply IHsatisfiesF; eauto.
Qed.

(* Requires coinduction because the forall and exist states *)
Lemma satisfies_TauR:
  forall (E : Type -> Type) (A : Type) (P : itree_spec E A) (t : itree E A),
    satisfies P (Tau t) ->
    satisfies P t.
Proof.
  intros E A. pcofix CIH. intros P t HP.
  pfold. red.
  punfold HP. red in HP. dependent induction HP; pclearbot; auto.
  - rewrite <- x. constructor. pstep_reverse. eapply paco2_mon; eauto.
    intuition.
  - rewrite <- x. constructor. eapply IHHP; eauto.
  - pstep_reverse. clear IHHP. eapply paco2_mon with (r := bot2); intuition.
  - rewrite <- x0. cbn in x. constructor. right.
    eapply CIH; eauto. pfold. red. cbn. rewrite <- x. pstep_reverse.
  - rewrite <- x0. constructor. destruct H as [x' Hx']. pclearbot.
    exists x'. right. eapply CIH. pfold. red. rewrite <- x. pstep_reverse.
Qed.

Lemma satisfies_eutt_spec_l E A (P1 P2:itree_spec E A) tree :
  satisfies P1 tree -> eutt eq P1 P2 -> satisfies P2 tree.
Proof.
  revert P1 P2 tree. pcofix CIH. intros P1 P2 tree HP HP12.
  punfold HP. red in HP. pfold. red. punfold HP12. red in HP12.
  dependent induction HP.
  - rewrite <- x. rewrite <- x0 in HP12. dependent induction HP12; auto.
    + rewrite <- x. constructor.
    + rewrite <- x. constructor. eapply IHHP12; eauto.
  - pclearbot.
    remember (observe P2) as oP2. clear HeqoP2 P2.
    assert ((exists P2', oP2 = TauF P2') \/ (forall P2', oP2 <> TauF P2') ).
    { destruct oP2; eauto; right; repeat intro; discriminate. }
    rewrite <- x. rewrite <- x0 in HP12. clear x0 x.
    destruct H0 as [ [P2' HP2'] | HP2' ].
    + subst. constructor. right. eapply CIH; eauto.
      rewrite <- tau_eutt. setoid_rewrite <- tau_eutt at 3.
      pfold. auto.
    + inversion HP12; try (exfalso; eapply HP2'; eauto; fail); subst.
       clear HP12. punfold H. red in H.
       dependent induction REL; intros; subst;
       try (exfalso; eapply HP2'; eauto; fail).
       * constructor. rewrite <- x in H.
         clear CIH HP2' x. dependent induction H; try constructor.
         ++ rewrite <- x. constructor.
         ++ rewrite <- x. constructor. apply IHsatisfiesF; auto.
       * rewrite <- x in H. constructor. pclearbot.
         eapply satisfies_eutt_spec_tau_vis_aux; eauto.
       * eapply IHREL; auto. rewrite <- x in H.
         eapply satisfiesF_TauL; eauto.
  - eapply IHHP; eauto. rewrite <- x in HP12.
    assert (Tau spec ≈ P2); try (pfold; auto; fail).
    rewrite tau_eutt in H. punfold H.
  - rewrite <- x. constructor. eapply IHHP; eauto.
  - rewrite <- x. rewrite <- x0 in HP12. dependent induction HP12.
    + rewrite <- x. constructor. pclearbot. intros.  right. eapply CIH; eauto.
      apply H.
    + rewrite <- x. constructor. eapply IHHP12; eauto.
  - rewrite <- x0 in HP12. dependent induction HP12.
    + rewrite <- x. constructor. pclearbot. intros. right. eapply CIH; eauto.
      pfold. red. rewrite <- x1.
      specialize (H x2). punfold H.
    + rewrite <- x. constructor. eapply IHHP12; eauto.
  - rewrite <- x0 in HP12. rewrite <- x. clear x tree. dependent induction HP12.
    + rewrite <- x. constructor. destruct H as [x' Hx']. pclearbot.
      exists x'. right. eapply CIH; eauto.
    + rewrite <- x. constructor. eapply IHHP12; eauto.
Qed.

Lemma satisfies_eutt_spec_r E A (P:itree_spec E A) (t1 t2 : itree E A) :
  satisfies P t1 -> t1 ≈ t2 -> satisfies P t2.
Proof.
  revert P t1 t2. pcofix CIH. intros P t1 t2 HP Ht12.
  pfold. red. punfold Ht12. red in Ht12. punfold HP. red in HP.
  dependent induction Ht12.
  - rewrite <- x. rewrite <- x0 in HP. clear x x0.
    dependent induction HP; auto;
    try (rewrite <- x; auto).
    + rewrite <- x0. pclearbot. constructor.
      intros. right. eapply CIH; try apply H. reflexivity.
    + rewrite <- x0. constructor. destruct H as [x' Hx']. pclearbot.
      exists x'. right. eapply CIH; eauto. reflexivity.
      (* Tau Tau case *)
  - pclearbot. remember (observe P) as oP. clear HeqoP P.
    assert ( (exists P, oP = TauF P) \/ (forall P, oP <> TauF P) ).
    { destruct oP; eauto; right; repeat intro; discriminate. }
    destruct H as [ [P HoP] | HoP].
    + subst. rewrite <- x. constructor. right. eapply CIH; eauto.
      apply satisfies_TauR. pfold. red. apply satisfiesF_TauL. simpl.
      rewrite x0. auto.
    + rewrite <- x. rewrite <- x0 in HP.
      inversion HP; try (exfalso; eapply HoP; eauto; fail).
      * subst. clear HP. clear x x0. punfold REL. red in REL. constructor.
        dependent induction H1; try (exfalso; eapply HoP; eauto; fail).
        ++ rewrite <- x in REL. clear x. dependent induction REL;
           try (rewrite <- x; auto).
        ++ eapply IHsatisfiesF; auto. pstep_reverse.
           assert (m1 ≈ m2); try (pfold; auto; fail). simpobs x. rewrite x in H.
           rewrite tau_eutt in H. auto.
        ++ rewrite <- x in REL. clear x. dependent induction REL.
           ** rewrite <- x; auto. constructor. right.
              pclearbot. eapply CIH; eauto. apply H.
           ** rewrite <- x. constructor. eapply IHREL; eauto.
        ++ pclearbot. constructor. right. eapply CIH; eauto. pfold. red.
           rewrite <- x. pstep_reverse.
        ++ constructor. destruct H as [x' Hx']. pclearbot. exists x'. right.
           eapply CIH; eauto. simpobs x. rewrite <- itree_eta in x. rewrite <- x.
           pfold. auto.
      * constructor. constructor. right. pclearbot. eapply CIH; eauto.
        apply satisfies_TauR. pfold. red. cbn. rewrite <- H. pstep_reverse.
      * constructor. constructor. destruct H1 as [x' Hx' ]. pclearbot.
        exists x'. right. eapply CIH; eauto. symmetry in H. simpobs H.
        rewrite H. rewrite tau_eutt. auto.
  - rewrite <- x. rewrite <- x0 in HP. clear x x0. dependent induction HP.
    + rewrite <- x. constructor. eapply IHHP; eauto.
    + rewrite <- x. constructor. intros. right.
      pclearbot. eapply CIH; eauto. apply H.
    + rewrite <- x0. pclearbot.
      assert (VisF e k2 = observe (Vis e k2) ); auto. rewrite H0.
      constructor. intros. right. eapply CIH; try apply H.
      symmetry in x. simpobs x. rewrite x.
      pfold. red. constructor. auto.
    + rewrite <- x0. assert (VisF e k2 = observe (Vis e k2) ); auto.
      rewrite H0. constructor. destruct H as [x' Hx']. pclearbot.
      exists x'. right. eapply CIH; eauto. symmetry in x. simpobs x.
      rewrite x. pfold. constructor. left. auto.
  - eapply IHHt12; auto. rewrite <- x in HP. pstep_reverse.
    apply satisfies_TauR. pfold. auto.
  - rewrite <- x. constructor.
    eapply IHHt12; eauto.
Qed.

Instance proper_eutt_satisfies E R : Proper (@eutt (SpecEvent E) R R eq ==> eutt eq ==> iff) satisfies.
Proof.
  intros P Q HPQ t1 t2 Ht12. split; intros.
  - eapply satisfies_eutt_spec_r; eauto. eapply satisfies_eutt_spec_l; eauto.
  - symmetry in HPQ. symmetry in Ht12. eapply satisfies_eutt_spec_r; eauto. eapply satisfies_eutt_spec_l; eauto.
Qed.


(** * `refines` and `refines_eq` **)

Definition refines {E A} (s1 s2 : itree_spec E A) : Prop :=
  forall t, satisfies s1 t -> satisfies s2 t.

Infix "|=" := refines (at level 70, no associativity).

Instance PreOrder_refines E A : PreOrder (@refines E A).
Proof.
  split; repeat intro; eauto.
Qed.

Instance Proper_observing_refines E A :
  Proper (observing eq ==> observing eq ==> iff) (@refines E A).
Proof.
  split; repeat intro.
  - rewrite <- H0. apply H1. rewrite H. eauto.
  - rewrite H0. apply H1. rewrite <- H. eauto.
Qed.

Instance Proper_eutt_refines E A :
  Proper (eutt eq ==> eutt eq ==> iff) (@refines E A).
Proof.
  split; repeat intro.
  - rewrite <- H0. apply H1. rewrite H. eauto.
  - rewrite H0. apply H1. rewrite <- H. eauto.
Qed.

Definition refines_eq {E A} (s1 s2 : itree_spec E A) := s1 |= s2 /\ s2 |= s1.

Infix "~=" := refines_eq (at level 70, no associativity).

Instance Equivalence_refines_eq E A : Equivalence (@refines_eq E A).
Proof.
  split; repeat intro.
  - split; reflexivity.
  - split; destruct H; eauto.
  - split; destruct H, H0.
    + rewrite H; exact H0.
    + rewrite H2; exact H1.
Qed.

Instance Proper_observing_refines_eq E A :
  Proper (observing eq ==> observing eq ==> iff) (@refines_eq E A).
Proof.
  split; repeat intro; unfold refines_eq.
  - rewrite <- H, <- H0; eauto.
  - rewrite H, H0; eauto.
Qed.

Instance Proper_eutt_refines_eq E A :
  Proper (eutt eq ==> eutt eq ==> iff) (@refines_eq E A).
Proof.
  split; repeat intro; unfold refines_eq.
  - rewrite <- H, <- H0; eauto.
  - rewrite H, H0; eauto.
Qed.

Instance Proper_refines_eq_refines E A :
  Proper (refines_eq ==> refines_eq ==> iff) (@refines E A).
Proof.
  split; destruct H, H0; intro.
  - rewrite H1, <- H0; eauto.
  - rewrite H, <- H2; eauto.
Qed.


(** * `refinesFun` and `refinesFun_eq` **)

Definition refinesFun {E A B} := pointwise_relation A (@refines E B).
Hint Unfold refinesFun : core.

Infix "|=1" := refinesFun (at level 70, no associativity).

Instance PreOrder_refinesFun E A B : PreOrder (@refinesFun E A B).
Proof.
  split; intro.
  - intro; reflexivity.
  - do 5 intro; transitivity (y a); eauto.
Qed.

Definition refinesFun_eq {E A B} := pointwise_relation A (@refines_eq E B).
Hint Unfold refinesFun_eq : core.

Infix "~=1" := refinesFun_eq (at level 70, no associativity).

Instance Equivalence_refinesFun_eq E A B : Equivalence (@refinesFun_eq E A B).
Proof.
  split; intro.
  - intro; reflexivity.
  - do 3 intro; symmetry; eauto.
  - do 5 intro; transitivity (y a); eauto.
Qed.


(** * `bind` is proper w.r.t. `refines` **)

(* The proposition that a is returned by an itree along some path *)
Inductive is_itree_retval' {E A} : itree' E A -> A -> Prop :=
| iirv_ret a : is_itree_retval' (RetF a) a
| iirv_tau tree a :
    is_itree_retval' (observe tree) a -> is_itree_retval' (TauF tree) a
| iirv_vis {X} (ev:E X) tree a x :
    is_itree_retval' (observe (tree x)) a ->
    is_itree_retval' (VisF ev tree) a
.

Definition is_itree_retval {E A} tree a := @is_itree_retval' E A (observe tree) a.

Instance Proper_observing_is_itree_retval E A :
  Proper (observing eq ==> eq ==> iff) (@is_itree_retval E A).
Proof.
  intros m1 m2 [ em ] a1 a2 ea. rewrite <- ea. unfold is_itree_retval.
  rewrite em. reflexivity.
Qed.

Lemma bind_satisfies_bind E A B (P:itree_spec E A) (Q:A -> itree_spec E B)
      (m:itree E A) (f:A -> itree E B) :
  satisfies P m ->
  (forall a, is_itree_retval m a -> satisfies (Q a) (f a)) ->
  satisfies (P >>= Q) (m >>= f).
Proof.
  intro sats; revert P m sats. pcofix CIH.
  intros P m sats satsQ; punfold sats. unfold satisfies_ at 1 in sats.
  remember (observe P) as obsP eqn: e_obsP.
  remember (observe m) as obsm eqn: e_obsm.
  revert P m e_obsP e_obsm satsQ. induction sats; intros.
  { rewrite <- (observing_intros _ (Ret a) _ e_obsP).
    rewrite <- (observing_intros _ (Ret a) _ e_obsm).
    repeat rewrite bind_ret_.
    eapply paco2_mon_bot; [ apply satsQ | intros; eassumption ].
    rewrite <- (observing_intros _ (Ret a) _ e_obsm). constructor. }
  { rewrite <- (observing_intros _ (Tau _) _ e_obsP).
    rewrite <- (observing_intros _ (Tau _) _ e_obsm).
    repeat rewrite bind_tau_.
    pfold. apply Satisfies_Tau. right. pclearbot. apply CIH; [ assumption | ].
    intros a iirv. apply satsQ.
    rewrite <- (observing_intros _ (Tau _) _ e_obsm).
    constructor. assumption. }
  { rewrite <- (observing_intros _ (Tau _) _ e_obsP). rewrite bind_tau_.
    pfold. apply Satisfies_TauL.
    set (IHapp := IHsats spec m eq_refl e_obsm satsQ). punfold IHapp. }
  { rewrite <- (observing_intros _ (Tau _) _ e_obsm). rewrite bind_tau_.
    pfold. apply Satisfies_TauR.
    assert (paco2 satisfies_ r (P >>= Q) (tree >>= f)) as IHapp;
      [ | punfold IHapp ].
    apply IHsats; [ assumption | reflexivity | ].
    intros. apply satsQ. rewrite <- (observing_intros _ (Tau _) _ e_obsm).
    constructor. assumption. }
  { rewrite <- (observing_intros _ (Vis _ _) _ e_obsP).
    rewrite <- (observing_intros _ (Vis _ _) _ e_obsm).
    repeat rewrite bind_vis_. pfold.
    apply Satisfies_Vis. intro x. right. apply CIH.
    - pclearbot. apply H.
    - intros. apply satsQ. rewrite <- (observing_intros _ (Vis _ _) _ e_obsm).
      econstructor. eassumption. }
  { rewrite <- (observing_intros _ (Vis _ _) _ e_obsP).
    rewrite <- (observing_intros _ _ _ e_obsm).
    rewrite bind_vis_. pfold. apply Satisfies_Forall. intro x. right. apply CIH.
    - pclearbot. apply H.
    - intros. apply satsQ.
      rewrite <- (observing_intros _ _ _ e_obsm). assumption. }
  { rewrite <- (observing_intros _ (Vis _ _) _ e_obsP).
    rewrite <- (observing_intros _ _ _ e_obsm).
    rewrite bind_vis_. pfold.
    destruct H as [ x H ]. apply Satisfies_Exists. exists x. right. apply CIH.
    - pclearbot. apply H.
    - intros. apply satsQ.
      rewrite <- (observing_intros _ _ _ e_obsm). assumption. }
Qed.

Instance Proper_refines_bind {E A B} :
  Proper ((pointwise_relation A refines) ==> @refines E A ==> @refines E B) ITree.bind'.
Proof.
  repeat intro; unfold pointwise_relation in H; unfold refines in *.
  revert x y H y0 H0 t H1. pcofix CIH; intros.
  case_eq (observe x0); intros; simpl.
  - rewrite (observing_intros eq x0 (Ret r0) H) in H2.
    rewrite unfold_bind in H2; simpl in H2.
    specialize (H0 _ t H2).
    replace t with (Ret r0 >> t) by admit.
    (* eapply bind_satisfies_bind. *)
    admit.
  - admit.
  - admit.
Admitted.

Instance Proper_refines_eq_bind {E A B} :
  Proper ((pointwise_relation A refines_eq) ==> @refines_eq E A ==> @refines_eq E B) ITree.bind'.
Proof.
  split; apply Proper_refines_bind; eauto.
  - intro; destruct (H a); eauto.
  - destruct H0; eauto.
  - intro; destruct (H a); eauto.
  - destruct H0; eauto.
Qed.


(** * `mrec` and `refines` **)

Lemma refines_mrec {D E} (ctx : D ~> itree (D +' SpecEvent E))
                         (g : D ~> itree_spec E) :
  (forall T d, interp (case_ g ITree.trigger) (ctx T d) |= g T d) ->
  (forall T d, mrec ctx d |= g T d).
Proof.
  (* Recall: mrec ctx d ≈ interp (case_ (mrec ctx) ITree.trigger) (ctx T d) *)
  intros. pcofix CIH. intros.
  unfold refines in H.
  rewrite mrec_as_interp in H1; unfold mrecursive in H1.
Admitted.


(** * `forall` and `exists` specs **)

Notation forall_spec k := (Vis Spec_forall k).

Lemma forall_spec_is_forall {E A B} (k : A -> itree_spec E B) t :
    satisfies (forall_spec k) t <-> forall a, satisfies (k a) t.
Proof.
  split; intros.
  - punfold H. red in H. pfold. red. cbn in H. dependent induction H.
    + rewrite <- x. constructor. eauto.
    + simpobs x. rewrite <- itree_eta in x. pclearbot. pstep_reverse.
      rewrite x. auto.
  - pfold. red. cbn. constructor. intros. specialize (H x). left. auto.
Qed.

(* Hey, this now holds in both directions with itrees! *)
Lemma forall_spec_bind {E A B C} (k1 : A -> itree_spec E B) (k2 : B -> itree_spec E C) :
    (forall_spec k1) >>= k2 ≈ forall_spec (fun a => (k1 a) >>= k2).
Proof.
  rewrite bind_vis. pfold. constructor.
  intros; left. apply Reflexive_eqit; eauto.
Qed.

Lemma refines_forall_spec_r {E A B} P (Q : A -> itree_spec E B) :
  (forall a, P |= Q a) -> P |= forall_spec Q.
Proof.
  repeat intro.
  apply forall_spec_is_forall.
  intro; apply H; eauto.
Qed.

Lemma refines_forall_spec_l {E A B} (P : A -> itree_spec E B) Q a :
  P a |= Q -> forall_spec P |= Q.
Proof.
  repeat intro.
  eapply forall_spec_is_forall in H0.
  apply H; eauto.
Qed.

Notation exists_spec k := (Vis Spec_exists k).

Lemma exists_spec_is_exists {E A B} (k : A -> itree_spec E B) t :
  satisfies (exists_spec k) t <-> exists a, satisfies (k a) t.
Proof.
  split; intros.
  - punfold H. red in H. cbn in *. dependent induction H; [ simpobs x | idtac ].
    + setoid_rewrite x. setoid_rewrite tau_eutt. eapply IHsatisfiesF; eauto.
    + simpobs x. rewrite <- itree_eta in x. setoid_rewrite x.
      destruct H; pclearbot; eauto.
  - pfold. red. cbn. constructor.
    destruct H; exists x; auto.
Qed.

Lemma exists_spec_bind {E A B C} (k1 : A -> itree_spec E B) (k2 : B -> itree_spec E C) :
    (exists_spec k1) >>= k2 ≈ exists_spec (fun a => k1 a >>= k2).
Proof.
  rewrite bind_vis. pfold. constructor.
  intros; left. apply Reflexive_eqit; eauto.
Qed.

Lemma refines_exists_spec_r {E A B} P (Q : A -> itree_spec E B) a :
  P |= Q a -> P |= exists_spec Q.
Proof.
  repeat intro.
  apply exists_spec_is_exists.
  exists a; auto.
Qed.

Lemma refines_exists_spec_l {E A B} (P : A -> itree_spec E B) Q :
  (forall a, P a |= Q) -> exists_spec P |= Q.
Proof.
  repeat intro.
  apply exists_spec_is_exists in H0; destruct H0.
  apply (H x); auto.
Qed.

Lemma refines_exists_spec_lr {E A B} (P Q : A -> itree_spec E B) :
  (forall a, P a |= Q a) -> exists_spec P |= exists_spec Q.
Proof.
  repeat intro.
  apply exists_spec_is_exists.
  apply exists_spec_is_exists in H0; destruct H0.
  exists x; apply (H x); auto.
Qed.


(** * `top` and `bottom` specs **)

CoFixpoint top_spec {E A} : itree_spec E A :=
  forall_spec (fun _ : unit => top_spec).

Lemma top_spec_is_top {E A} (t : itree E A) : satisfies top_spec t.
Proof.
  pcofix CIH. intros. pfold. red. cbn. constructor. intros. right. auto.
Qed.

Lemma refines_top_spec_r {E A} (k : itree_spec E A) : k |= top_spec.
Proof.
  repeat intro. apply top_spec_is_top.
Qed.

Definition bottom_spec {E A} : itree_spec E A :=
  exists_spec (fun v : void => match v with end).

Lemma bottom_spec_is_bottom {E A} (t : itree E A) : ~ satisfies bottom_spec t.
Proof.
  intros Hcontra. punfold Hcontra. red in Hcontra. cbn in *. dependent induction Hcontra; eauto.
  destruct H as [ [] _ ].
Qed.

Lemma refines_bottom_spec_l {E A} (k : itree_spec E A) : bottom_spec |= k.
Proof.
  repeat intro. apply bottom_spec_is_bottom in H. inversion H.
Qed.


(** * `and` and `or` specs **)

Definition and_spec {E A} (P Q : itree_spec E A) :=
  forall_spec (fun b : bool => if b then P else Q).

Lemma and_spec_is_and {E A} (t : itree E A) (P Q : itree_spec E A) :
    satisfies (and_spec P Q) t <-> (satisfies P t /\ satisfies Q t).
Proof.
  split; intros; [split | destruct H].
  - apply (proj1 (forall_spec_is_forall _ _) H true).
  - apply (proj1 (forall_spec_is_forall _ _) H false).
  - apply forall_spec_is_forall; destruct a; eauto.
Qed.

Lemma and_spec_bind {E A B} (P Q : itree_spec E A) (k : A -> itree_spec E B) :
    (and_spec P Q) >>= k ≈ and_spec (P >>= k) (Q >>= k).
Proof.
  unfold and_spec.
  rewrite forall_spec_bind.
  apply eqit_Vis.
  destruct u; reflexivity.
Qed.

Lemma refines_and_spec_r {E A} k (P Q : itree_spec E A) :
  k |= P -> k |= Q -> k |= and_spec P Q.
Proof.
  intros; apply refines_forall_spec_r.
  destruct a; eauto.
Qed.

Lemma refines_and_spec_l {E A} (P Q : itree_spec E A) k :
  P |= k \/ Q |= k -> and_spec P Q |= k.
Proof.
  destruct 1.
  - apply (refines_forall_spec_l _ _ true); eauto.
  - apply (refines_forall_spec_l _ _ false); eauto.
Qed.

Definition or_spec {E A} (P Q : itree_spec E A) :=
  exists_spec (fun b : bool => if b then P else Q).

Lemma or_spec_is_or {E A} (t : itree E A) (P Q : itree_spec E A) :
    satisfies (or_spec P Q) t <-> (satisfies P t \/ satisfies Q t).
Proof.
  split; intros; [|destruct H].
  - pose proof (proj1 (exists_spec_is_exists _ _) H).
    destruct H0 as [[]]; eauto.
  - apply exists_spec_is_exists; exists true; eauto.
  - apply exists_spec_is_exists; exists false; eauto.
Qed.

Lemma or_spec_bind {E A B} (P Q : itree_spec E A) (k : A -> itree_spec E B) :
    (or_spec P Q) >>= k ≈ or_spec (P >>= k) (Q >>= k).
Proof.
  unfold or_spec.
  rewrite exists_spec_bind.
  apply eqit_Vis.
  destruct u; reflexivity.
Qed.

Lemma refines_or_spec_r {E A} k (P Q : itree_spec E A) :
  k |= P \/ k |= Q -> k |= or_spec P Q.
Proof.
  destruct 1.
  - apply (refines_exists_spec_r _ _ true); eauto.
  - apply (refines_exists_spec_r _ _ false); eauto.
Qed.

Lemma refines_or_spec_l {E A} (P Q : itree_spec E A) k :
  P |= k -> Q |= k -> or_spec P Q |= k.
Proof.
  intros; apply refines_exists_spec_l.
  destruct a; eauto.
Qed.


(** * `assert` and `assuming` specs **)

Definition assert_spec {E} (P : Prop) : itree_spec E unit :=
  exists_spec (fun pf : P => Ret tt).

Lemma iwish {E A} (P : Prop) (k : itree_spec E A) :
  exists_spec (fun pf : P => k) ~= assert_spec P >> k.
Proof.
  split; unfold assert_spec;
  rewrite bind_vis;
  eapply refines_exists_spec_lr; intro;
  rewrite bind_ret_l; reflexivity.
Qed.

Definition assert_spec_refines_eq {E} (P : Prop) (pf : P) :
  @assert_spec E P ~= Ret tt.
Proof.
  split; repeat intro.
  - apply exists_spec_is_exists in H; destruct H; eauto.
  - apply exists_spec_is_exists; exists pf; eauto.
Qed.

Lemma refines_bind_assert_spec_r {E A} (P : Prop) (k1 k2 : itree_spec E A) :
  P -> k1 |= k2 -> k1 |= assert_spec P >> k2.
Proof.
  intros pf ?.
  rewrite <- iwish.
  apply refines_exists_spec_r; eauto.
Qed.

Lemma refinesM_bindM_assertM_l {A} (P:Prop) (m1 m2: CompM A) :
  (P -> m1 |= m2) -> assertM P >> m1 |= m2.
Proof.
  intro H. unfold assertM; rewrite existsM_bindM.
  apply refinesM_existsM_l.
  rewrite returnM_bindM; assumption.
Qed.

Definition assumingM {A} (P:Prop) (m:CompM A) : CompM A :=
  forallM (fun pf:P => m).

Lemma refinesM_assumingM_r {A} (P:Prop) (m1 m2: CompM A) :
  (P -> m1 |= m2) -> m1 |= assumingM P m2.
Proof.
  apply refinesM_forallM_r.
Qed.

Lemma refinesM_assumingM_l {A} (P:Prop) (m1 m2 : CompM A) :
  P -> m1 |= m2 -> assumingM P m1 |= m2.
Proof.
  apply refinesM_forallM_l.
Qed.





(** * misc. stuff below **)

Notation " x : T <- m1 ;; m2" := (ITree.bind m1 (fun x : T=> m2) ) (at level 40).

Section l_bind_satisfies_bind_counter.
  Variant NonDet : Type -> Type := Choose : NonDet bool.

  Definition m_counter : itree NonDet unit :=
    x : bool <- ITree.trigger Choose ;;
    if x then Ret tt else y : bool <- ITree.trigger Choose;; Ret tt.

  Definition P_counter : itree_spec NonDet unit :=
    x : bool <- ITree.trigger (Spec_vis Choose);; Ret tt.

  Definition Q_counter : unit -> itree_spec NonDet unit :=
    fun _ => or_spec (Ret tt) ( x : bool <- ITree.trigger (Spec_vis Choose);; Ret tt  ).

  Lemma m_counter_sats_P_bind_Q_counter : satisfies (P_counter >>= Q_counter) m_counter.
  Proof.
    pfold. red. cbn. constructor. left. destruct x.
    - pfold. red. cbn.
      assert (RetF (E:= NonDet) tt = observe (Ret tt)); auto.
      rewrite H. constructor. exists true. left. pfold; constructor.
    - pfold. red. cbn. assert (VisF Choose (fun x : bool => _ : bool <- Ret x;; Ret tt) =
                               observe (Vis Choose (fun x : bool => _ : bool <- Ret x;; Ret tt) ) ); auto.
      rewrite H. constructor. exists false. left. pfold. red. cbn.
      rewrite H. constructor. intros [ | ]; left; pfold; red; cbn; auto.
   Qed.

  Lemma satifies_P_counter : forall m, satisfies P_counter m ->
                                  m ≈ (x : bool <- ITree.trigger Choose;; Ret tt).
  Proof.
    intros. unfold P_counter in *. punfold H. red in H. pfold. red. cbn in *.
    dependent induction H.
    - rewrite <- x. constructor; auto.
    - rewrite <- x. constructor. left. pclearbot. specialize (H v).
      assert (satisfies (_ : bool <- Ret v;; Ret tt) (tree v) ); auto.
      enough (tree v ≈ ( _ : bool <- Ret v;; Ret tt) ); auto. rewrite bind_ret_l.
      rewrite bind_ret_l in H0. symmetry. clear x H m.
      pfold. red. punfold H0. red in H0. cbn in *.
      remember (observe (tree v) ) as ot. clear Heqot tree v. dependent induction H0; auto.
  Qed.

  Definition m0_counter : itree NonDet unit := x : bool <- ITree.trigger Choose;; Ret tt.

  Lemma m0_counter_no_continuation : forall k,
      ~ m0_counter >>= k ≈ m_counter .
  Proof.
    unfold m0_counter, m_counter.
    intros k Hcontra. repeat rewrite bind_trigger in Hcontra.
    rewrite bind_vis in Hcontra. apply eqit_inv_vis in Hcontra as [_ Hcontra] .
    specialize (Hcontra true) as Hktrue. specialize (Hcontra false) as Hkfalse.
    cbn in *. rewrite bind_ret_l in Hktrue. rewrite bind_ret_l in Hkfalse.
    rewrite Hktrue in Hkfalse. pinversion Hkfalse.
  Qed.

  Lemma not_l_bind_satisfies_bind_aux : exists E R S
               (m : itree E R) (P : itree_spec E S) (Q : S -> itree_spec E R),
      satisfies (P >>= Q) m /\ (forall m0 k, satisfies P m0 -> ~ (m0 >>= k ≈ m) ).
    Proof.
      exists NonDet, unit, unit, m_counter, P_counter, Q_counter.
      split; try apply m_counter_sats_P_bind_Q_counter.
      intros. apply satifies_P_counter in H. rewrite H. fold m0_counter.
      apply m0_counter_no_continuation.
    Qed.


End l_bind_satisfies_bind_counter.

Lemma not_l_bind_satisfies_bind : ~ forall E R S
            (m : itree E R) (P : itree_spec E S) (Q : S -> itree_spec E R),
       satisfies (P >>= Q) m -> exists m0 k, satisfies P m0 /\ (forall a, is_itree_retval m0 a -> satisfies (Q a) (k a) ) /\ (m0 >>= k ≈ m).
Proof.
  destruct not_l_bind_satisfies_bind_aux as [ E [R [S [m [P [Q  [H0 H1] ] ] ] ] ] ].
  intros Hcontra. specialize (Hcontra E R S m P Q H0).
  destruct Hcontra as [m0 [k [Hsat [ _ Heutt] ] ] ]. eapply H1; eauto.
Qed.

(* Our event type = errors *)
Inductive CompMEvent : Type -> Type :=
| ErrorEvent : CompMEvent False
.

(* Our computations are sets of ITrees. That is, they are really more like
specifications of computations *)
Definition CompM (A:Type) : Type := itree_spec CompMEvent A.
