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

Variant satisfiesF {E A} (satisfies : itree_spec E A -> itree E A -> Prop)
  : itree_spec E A -> itree E A -> Prop :=
| Satisfies_Ret a : satisfiesF satisfies (Ret a) (Ret a)
| Satisfies_TauL spec tree :
    satisfies spec tree -> satisfiesF satisfies (Tau spec) tree
| Satisfies_TauR spec tree :
    satisfies spec tree -> satisfiesF satisfies spec (Tau tree)
| Satisfies_Vis X (e:E X) spec tree :
    (forall x, satisfies (spec x) (tree x)) ->
    satisfiesF satisfies (Vis (Spec_vis e) spec) (Vis e tree)
| Satisfies_Forall X spec tree :
    (forall x:X, satisfies (spec x) tree) ->
    satisfiesF satisfies (Vis Spec_forall spec) tree
| Satisfies_Exists X spec tree :
    (exists x:X, satisfies (spec x) tree) ->
    satisfiesF satisfies (Vis Spec_exists spec) tree
.

Definition satisfies {E A} spec tree := paco2 (@satisfiesF E A) bot2 spec tree.

Lemma satisfiesF_mono E A : monotone2 (@satisfiesF E A).
Proof.
  intros spec tree r1 r2 sats sub12. destruct sats; constructor.
  { apply sub12. assumption. }
  { apply sub12. assumption. }
  { intros; apply sub12. apply H. }
  { intros; apply sub12. apply H. }
  { destruct H as [ x H ]. exists x. apply sub12. apply H. }
Qed.

Hint Resolve satisfiesF_mono : paco.

(* The proposition that a is returned by an itree along some path *)
Inductive is_itree_retval {E A} : itree E A -> A -> Prop :=
| iirv_ret a : is_itree_retval (Ret a) a
| iirv_tau itree a : is_itree_retval itree a -> is_itree_retval (Tau itree) a
| iirv_vis {X} (ev:E X) itree a x : is_itree_retval (itree x) a ->
                                    is_itree_retval (Vis ev itree) a
.

Infix ">>=" := ITree.bind (at level 58, left associativity).
Notation "m1 >> m2" := (m1 >>= fun _ => m2) (at level 58, left associativity).

Lemma satisfies_untau_l' E A spec tree (sats:@satisfies E A spec tree) spec' :
  spec = Tau spec' -> satisfies spec' tree.
Proof.
  revert spec tree sats spec'; pcofix CIH; intros.
  punfold sats. destruct sats; try discriminate.
  - injection H0; intro e; rewrite <- e.
    pclearbot.
    eapply paco2_mon_bot; [ eassumption | intros; assumption ].
  - pfold. apply Satisfies_TauR. pclearbot. right.
    apply (CIH _ _ H). assumption.
Qed.

Lemma satisfies_untau_l E A spec tree :
  @satisfies E A (Tau spec) tree ->
  satisfies spec tree.
Proof.
  intros sats. apply (satisfies_untau_l' E A _ _ sats _ eq_refl).
Qed.

Lemma satisfies_untau_r' E A spec tree (sats:@satisfies E A spec tree) tree' :
  tree = Tau tree' -> satisfies spec tree'.
Proof.
  revert spec tree sats tree'; pcofix CIH; intros.
  punfold sats. destruct sats; try discriminate.
  - pfold. apply Satisfies_TauL. right. pclearbot. apply (CIH _ _ H). assumption.
  - injection H0; intro e. rewrite <- e. pclearbot.
    eapply paco2_mon_bot; [ eassumption | intros; assumption ].
  - pfold. apply Satisfies_Forall; intro. right.
    pclearbot. apply (CIH _ _ (H x)). assumption.
  - destruct H as [ x H ]. pfold. apply Satisfies_Exists. exists x.
    pclearbot. right. apply (CIH _ _ H). assumption.
Qed.

Lemma satisfies_untau_r E A spec tree :
  @satisfies E A spec (Tau tree) ->
  satisfies spec tree.
Proof.
  intros sats. apply (satisfies_untau_r' E A _ _ sats _ eq_refl).
Qed.

Lemma satisfies_eutt_l E A spec tree (sats:@satisfies E A spec tree)
           spec' (e:eutt eq spec spec') :
  satisfies spec' tree.
Proof.
  (*
  revert spec tree sats spec' e; pcofix CIH; intros.
  punfold e. unfold eqit_ in e. rewrite itree_eta.
  destruct e.
  { unfold satisfies in sats.
    eapply paco2_mon_bot; [ eassumption | ].
  destruct e.
   *)
Admitted.

Lemma satisfies_eutt_r E A spec tree
           (sats:@satisfies E A spec tree)
           tree' (e:eutt eq tree tree') :
  satisfies spec tree'.
Proof.
Admitted.

Instance Proper_eutt_satisfies_impl E A :
  Proper (eutt eq ==> eutt eq ==> iff) (@satisfies E A).
Proof.
  intros spec1 spec2 e_spec tree1 tree2 e_tree.
  split; intro H.
  - eapply satisfies_eutt_l; [ | eassumption ].
    eapply satisfies_eutt_r; [ | eassumption ].
    assumption.
  - eapply satisfies_eutt_l; [ | symmetry; eassumption ].
    eapply satisfies_eutt_r; [ | symmetry; eassumption ].
    assumption.
Qed.

Instance Proper_eutt_paco2_satisfies_impl E A r :
  Proper (eutt eq ==> eutt eq ==> iff) (paco2 (@satisfiesF E A) r).
Proof.
Admitted.

Lemma bind_satisfies_bind E A B (P:itree_spec E A) (Q:A -> itree_spec E B)
      (m:itree E A) (f:A -> itree E B) :
  satisfies P m ->
  (forall a, is_itree_retval m a -> satisfies (Q a) (f a)) ->
  satisfies (P >>= Q) (m >>= f).
Proof.
  intro sats; revert P m sats. pcofix CIH.
  intros P m sats; punfold sats; destruct sats; intros.
  { rewrite bind_ret_l. rewrite bind_ret_l.
    eapply paco2_mon_bot; [ apply H0; constructor | intros; assumption ]. }
  { rewrite bind_tau. pfold. apply Satisfies_TauL. pclearbot. right.
    apply CIH; assumption. }
  { rewrite bind_tau. pfold. apply Satisfies_TauR. pclearbot. right.
    apply CIH; [ assumption | ]. intros. apply H0. apply iirv_tau; assumption. }
  { rewrite bind_vis. rewrite bind_vis. pfold. pclearbot.
    apply Satisfies_Vis. intro. right. apply CIH; [ apply H | ].
    intros a iirv. apply H0.
    apply (iirv_vis _ _ _ x). assumption. }
  { rewrite bind_vis. pfold. pclearbot. apply Satisfies_Forall. intros. right.
    apply CIH; [ apply (H x) | apply H0 ]. }
  { rewrite bind_vis. pfold. pclearbot. apply Satisfies_Exists.
    destruct H as [ x H ]. exists x. right. pclearbot.
    apply CIH; [ apply H | apply H0 ]. }
Qed.



(* Our event type = errors *)
Inductive CompMEvent : Type -> Type :=
| ErrorEvent : CompMEvent False
.

(* Our computations are sets of ITrees. That is, they are really more like
specifications of computations *)
Definition CompM (A:Type) : Type := itree_spec CompMEvent A.
