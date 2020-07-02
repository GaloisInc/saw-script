(***
 *** A version of the computation monad using the option-set monad
 ***)

From Coq Require Export Morphisms Setoid.
From ITree Require Export ITree ITreeFacts.
From Paco Require Import paco.

Variant SpecEvent (E:Type -> Type) (A:Type) : Type :=
| Spec_vis : E A -> SpecEvent E A
| Spec_forall : SpecEvent E A
| Spec_exists : SpecEvent E A
.

Arguments Spec_vis {E A}.
Arguments Spec_forall {E A}.
Arguments Spec_exists {E A}.

(* An ITree that defines a set of ITrees *)
Definition itree_spec E A : Type := itree (SpecEvent E) A.

(* The body of an itree_spec, inside the observe projection *)
Definition itree_spec' E A : Type := itree' (SpecEvent E) A.

Variant satisfiesF {E A} (satisfies : itree_spec E A -> itree E A -> Prop)
  : itree_spec' E A -> itree' E A -> Prop :=
| Satisfies_Ret a : satisfiesF satisfies (RetF a) (RetF a)
| Satisfies_TauL spec tree :
    satisfies spec tree ->
    satisfiesF satisfies (TauF spec) (observe tree)
| Satisfies_TauR spec tree :
    satisfies spec tree ->
    satisfiesF satisfies (observe spec) (TauF tree)
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

Instance Proper_satisfies_satisfiesF {E A} :
  Proper (pointwise_relation _ (pointwise_relation _ Basics.impl) ==>
          eq ==> eq ==> Basics.impl) (@satisfiesF E A).
Proof.
  intros R1 R2 implR spec1 spec2 e_spec tree1 tree2 e_tree sats.
  rewrite <- e_spec; rewrite <- e_tree.
  destruct sats; constructor; intros; try (apply implR; apply H).
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
  intros spec tree r1 r2 sats sub12. unfold satisfies_. destruct sats; constructor.
  { apply sub12; assumption. }
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

Lemma observing_eta {E A} (tree:itree E A) : observing eq tree (go (observe tree)).
Proof.
  constructor. reflexivity.
Qed.

Lemma observing_fun_eta {E A B} (tree:A -> itree E B) :
  pointwise_relation A (observing eq) tree (fun x => go (observe (tree x))).
Proof.
  intro a. constructor. reflexivity.
Qed.



Lemma satisfies_inv_tau_l E A (P:itree_spec E A) m :
  satisfies (Tau P) m -> satisfies P m.
Proof.
  revert P m; pcofix CIH; intros. punfold H0. inversion H0.
  { rewrite <- (observing_intros _ _ _ H1). pclearbot.
    eapply paco2_mon_bot; intros; eassumption. }
  { rewrite <- (observing_intros _ (Tau tree) _ H1). pfold.
    apply Satisfies_TauR. right. apply CIH. pclearbot. unfold satisfies.
    rewrite <- (observing_intros _ _ (Tau P) H). assumption. }
Qed.

(*
Lemma satisfies_inv_vis_l E A e X (P:X -> itree_spec E A) m :
  satisfies (Vis e P) m -> exists m', 

Lemma satisfies_eutt_l E A (P1 P2:itree_spec E A) (e: eutt eq P1 P2) :
  forall m, satisfies P1 m -> satisfies P2 m.
Proof.
  revert P1 P2 e; pcofix CIH. intros P1 P2 e.
  pose (e' := e).
  punfold e'. inversion e'; intros.
  { rewrite <- (observing_intros _ (Ret r2) _ H). rewrite <- REL.
    rewrite (observing_intros _ (Ret r1) _ H0).
    eapply paco2_mon_bot; intros; eassumption. }
  { rewrite <- (observing_intros _ (Tau m2) _ H). pfold.
    apply Satisfies_TauL. right. apply (CIH m1).
    - pclearbot. apply REL.
    - unfold satisfies in H1. rewrite <- (observing_intros _ (Tau m1) _ H0) in H1.
      apply satisfies_inv_tau_l. apply H1. }
  { unfold satisfies in H1. rewrite <- (observing_intros _ (Vis e0 k1) _ H0) in H1.
    punfold H1. inversion H1.
    - rewrite <- (observing_intros _ (Tau tree) _ H3).
      rewrite <- (observing_intros _ (Vis e0 k2) _ H).
      pfold. apply Satisfies_TauR.
      pclearbot. left.

      rewrite (observing_intros _ (Vis e0 k2) _ H)


rewrite <- (observing_intros _ (Vis e0 k2) _ H).
    - rewrite <- (observing_intros _ (Tau tree) _ H3).
    apply Satisfies


Lemma satisfies_eutt_l' E A (P1 P2:itree_spec' E A)
      (e: eqitF eq true true id (eutt eq) P1 P2) :
  forall m, satisfies (go P1) m -> satisfies (go P2) m.
Proof.
  revert P1 P2 e; pcofix CIH. intros P1 P2 e m sats. induction e.
  { rewrite <- REL. eapply paco2_mon_bot; [ eassumption | intros; assumption ]. }
  { pfold. apply Satisfies_TauL. right. apply CIH.
FIXME: can't apply CIH, because the argument to Tau is not of the form (go _)

punfold sats. inversion sats.
*)

Instance Proper_eutt_satisfies E A : Proper (eutt eq ==> eutt eq ==> iff) (@satisfies E A).
Admitted.

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


Infix ">>=" := ITree.bind (at level 58, left associativity).
Notation "m1 >> m2" := (m1 >>= fun _ => m2) (at level 58, left associativity).


(* FIXME: this is not actually true! *)
Instance Proper_observing_TauF E A : Proper (observing eq ==> eq)
                                            (TauF (E:=E) (R:=A) (itree:=itree E A)).
Proof.
Admitted.

(* FIXME: this is not actually true! *)
Instance Proper_observing_VisF E A X :
  Proper (eq ==> pointwise_relation X (observing eq) ==> eq)
         (VisF (E:=E) (R:=A) (itree:=itree E A) (X:=X)).
Proof.
Admitted.

Lemma bind_satisfies_bind' E A B (P:itree_spec' E A) (Q:A -> itree_spec E B)
      (m:itree' E A) (f:A -> itree E B) :
  satisfiesF satisfies P m ->
  (forall a, is_itree_retval' m a -> satisfies (Q a) (f a)) ->
  satisfies (go P >>= Q) (go m >>= f).
Proof.
  intro sats; revert P m sats. pcofix CIH.
  intros P m sats; destruct sats; intros.
  { repeat rewrite bind_ret_. eapply paco2_mon_bot; [ | intros; eassumption ].
    apply H0. constructor. }
  { rewrite (observing_eta spec). rewrite bind_tau_. pfold. apply Satisfies_TauL. right.
    apply CIH; [ | apply H0 ]. punfold H. unfold satisfies_ in H.
    eapply satisfiesF_mono; [ | eassumption ].
    intros s t sats. pclearbot. apply sats. }
  { rewrite (observing_eta tree). rewrite bind_tau_. pfold. apply Satisfies_TauR. right.
    apply CIH.
    - punfold H. eapply satisfiesF_mono; [ | eassumption ].
      intros. pclearbot. assumption.
    - intros. apply H0. apply iirv_tau; assumption. }
  { rewrite (observing_fun_eta spec). rewrite (observing_fun_eta tree).
    rewrite bind_vis_. rewrite bind_vis_. pfold.
    apply Satisfies_Vis. intro. right. apply CIH.
    - pose (sats := H x). punfold sats. eapply satisfiesF_mono; [ | eassumption ].
      intros; pclearbot; assumption.
    - intros; apply H0. eapply iirv_vis. eassumption. }
  { rewrite (observing_fun_eta spec). rewrite bind_vis_. pfold.
    apply Satisfies_Forall. intros. right.
    apply CIH; [ | apply H0 ].
    pose (sats := H x). punfold sats. eapply satisfiesF_mono; [ | eassumption ].
    intros. pclearbot. assumption. }
  { rewrite (observing_fun_eta spec). rewrite bind_vis_. pfold.
    apply Satisfies_Exists.
    destruct H as [ x sats ]. exists x. right.
    apply CIH; [ | apply H0 ].
    punfold sats. eapply satisfiesF_mono; [ | eassumption ].
    intros. pclearbot. assumption. }
Qed.


(* Our event type = errors *)
Inductive CompMEvent : Type -> Type :=
| ErrorEvent : CompMEvent False
.

(* Our computations are sets of ITrees. That is, they are really more like
specifications of computations *)
Definition CompM (A:Type) : Type := itree_spec CompMEvent A.
