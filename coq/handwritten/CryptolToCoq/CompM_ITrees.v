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

Instance Proper_observing_upaco2_satisfies_impl E A r :
  Proper (observing eq ==> observing eq ==> iff) (upaco2 (@satisfies_ E A) r).
Proof.
Admitted.

Instance Proper_observing_satisfies E A :
  Proper (observing eq ==> observing eq ==> iff) (@satisfies E A).
Proof.
  apply Proper_observing_paco2_satisfies_impl.
Qed.

(* FIXME: no longer needed? *)
Lemma observing_eta {E A} (tree:itree E A) : observing eq tree (go (observe tree)).
Proof.
  constructor. reflexivity.
Qed.

(* FIXME: no longer needed? *)
Lemma observing_fun_eta {E A B} (tree:A -> itree E B) :
  pointwise_relation A (observing eq) tree (fun x => go (observe (tree x))).
Proof.
  intro a. constructor. reflexivity.
Qed.

(* Two itrees are weakly bisimilar, where we only remove Taus from their heads,
i.e., before the first non-tau step *)
Definition eutt_head {E A} (t1 t2:itree E A) : Prop :=
  eqitF eq true true id eq (observe t1) (observe t2).

(* Two itrees are weakly bisimilar, where we only remove Taus from their tails,
i.e., after the first non-tau step *)
Definition eutt_tail {E A} (t1 t2:itree E A) : Prop :=
  eqitF eq false false id (eutt eq) (observe t1) (observe t2).

(* Split a weak bisimulation into head and tail bits *)
Lemma eutt_split E A (t1 t2:itree E A) (e:eutt eq t1 t2) :
  exists2 t1',
  eutt_head t1 t1' &
  exists2 t2', eutt_head t2 t2' & eutt_tail t1' t2'.
Proof.
  unfold eutt_head, eutt_tail.
  punfold e. unfold eqit_ in e.
  revert e. set (obs1 := observe t1). set (obs2 := observe t2).
  intro e; induction e.
  { exists (Ret r1); [ reflexivity | ]. exists (Ret r2); [ reflexivity | ].
    rewrite REL; reflexivity. }
  { exists (Tau m1); [ reflexivity | ]; exists (Tau m2); [ reflexivity | ].
    constructor. pclearbot. apply REL. }
  { exists (Vis e k1); [ reflexivity | ]; exists (Vis e k2); [ reflexivity | ].
    constructor. intro. pclearbot. apply REL. }
  { destruct IHe as [ t1' e1 [ t2' e2 e12 ]].
    exists t1'; [ repeat constructor; assumption | ].
    exists t2'; [ repeat constructor | ]; assumption. }
  { destruct IHe as [ t1' e1 [ t2' e2 e12 ]].
    exists t1'; [ repeat constructor; assumption | ].
    exists t2'; [ repeat constructor | ]; assumption. }
Qed.


Lemma satisfies_tau_l E A (P:itree_spec E A) m r :
  paco2 satisfies_ r P m -> paco2 satisfies_ r (Tau P) m.
Proof.
  intro sats; pinversion sats.
  { pfold. constructor. apply sats. }
  { pfold. constructor. assumption. }
  { pfold. constructor. rewrite <- H. constructor. assumption. }
  { rewrite <- (observing_intros _ (Tau tree) _ H). pfold. constructor. left.
    pfold. assumption. }
  { rewrite <- (observing_intros _ (Vis _ _) _ H0). pfold. constructor.
    rewrite <- H. constructor. intro x. apply H1. }
  { pfold. constructor. rewrite <- H. constructor. intro x.
    rewrite <- (observing_intros _ _ _ H0). apply H1. }
  { pfold. constructor. rewrite <- H. constructor.
    destruct H1 as [ x H1 ]. exists x.
    rewrite <- (observing_intros _ _ _ H0). assumption. }
Qed.


Lemma satisfies_tau_r E A (P:itree_spec E A) m r :
  paco2 satisfies_ r P m -> paco2 satisfies_ r P (Tau m).
Proof.
  intro sats; pinversion sats.
  { pfold. constructor. apply sats. }
  { pfold. constructor. assumption. }
  { rewrite <- (observing_intros _ (Tau spec) _ H). pfold. constructor. left.
    pfold. assumption. }
  { pfold. constructor. rewrite <- H. constructor. assumption. }
  { rewrite <- (observing_intros _ (Vis _ _) _ H). pfold. constructor.
    rewrite <- H0. constructor. intro x. apply H1. }
  { rewrite <- (observing_intros _ (Vis _ _) _ H). pfold. constructor.
    rewrite <- H0. constructor. intro x. apply H1. }
  { rewrite <- (observing_intros _ (Vis _ _) _ H). pfold. constructor.
    rewrite <- H0. destruct H1 as [ x H1 ]. constructor. exists x. assumption. }
Qed.

Lemma satisfies_inv_tau_l E A (P:itree_spec E A) m r :
  paco2 satisfies_ r (Tau P) m -> paco2 satisfies_ r P m.
Proof.
(*
  revert P m; pcofix CIH; intros P m sats.
  punfold sats. revert sats. unfold satisfies_.
  remember (observe m) as obsm eqn: e_obsm.
  rewrite <- (observing_intros _ (go obsm) _ e_obsm).
  remember (observe P) as obsP eqn: e_obsP.
  simpl. remember (TauF P) as tauP eqn: e_tauP.
  intro sats. revert P e_tauP e_obsP. induction sats; intros; try discriminate.
  { injection e_tauP; intro e_P; rewrite e_P in H.
    pfold. constructor. pclearbot. 
    

    rewrite e_obsP.


  (* remember (observe P2) as obsP2 eqn: e_obsP2 in sats. *)
  remember (observe tree) as obs_tree eqn: e_obs_tree in sats.

 sats.

pinversion sats.
  { rewrite <- (observing_intros _ (Tau tree) _ H0).
    eapply paco2_mon_bot; [ | intros; eassumption ].
    pfold. constructor. punfold H1. }
  { eapply paco2_mon_bot; [ | intros; eassumption ].
    pfold. apply H0. }
  { pclearbot. 


    eapply paco2_mon_bot; [ | intros; eassumption ].
    pfold. constructor. punfold sats. apply H1.


  intro sats; punfold sats. revert sats; unfold satisfies_.
  remember (observe m) as obsm eqn: e_obsm.
  remember (observe (Tau P)) as obsTP1 eqn: e_obsTP1.
  intro sats; revert P m e_obsm e_obsTP1; induction sats; intros; try discriminate.
  { injection e_obsTP1; intro e_spec. rewrite <- e_spec.
    rewrite <- (observing_intros _ (Tau tree) _ e_obsm).
    pfold; pclearbot; punfold H. constructor. apply H. }
  { injection e_obsTP1; intro e_spec. rewrite <- e_spec.

    injection e_obsm; intro e_m.
    constructor. pclearbot. apply H.

apply H.

  revert P m; pcofix CIH; intros. punfold H0. unfold satisfies_ in H0.
  induction 
*)
Admitted.

Lemma satisfies_vis_spec_funext E A X e (k1 k2 : X -> itree (SpecEvent E) A) tree r :
  (forall v, k1 v = k2 v) ->
  paco2 satisfies_ r (Vis e k1) tree ->
  paco2 satisfies_ r (Vis e k2) tree.
Proof.
  intros funext sats. punfold sats; unfold satisfies_ in sats at 1.
  simpl in sats. remember (VisF e k1) as obs1 eqn: e_obs1.
  remember (observe tree) as obs_t eqn: e_obs_t.
  revert e_obs1 tree e_obs_t. induction sats; intros; try discriminate.
  { rewrite <- (observing_intros _ (Tau tree) _ e_obs_t). pfold.
    apply Satisfies_TauR.
    assert (paco2 satisfies_ r (Vis e k2) tree) as IHapp; [ | punfold IHapp ].
    apply IHsats; [ assumption | reflexivity ]. }
  { rewrite <- (observing_intros _ (Vis _ _) _ e_obs_t).
    destruct e; try discriminate.
(*
pfold.

    set (IHapp := IHsats e k1 k2 e_obs1 tree eq_refl). punfold IHapp. }
  { rewrite <- (observing_intros _ (Vis _ _) _ e_obs_t). pfold.
    injection e_obs1. intros.
    dependent rewrite H2.
    apply Satisfies_Vis.

  clear e_obs_t.
  intro sats; induction sats; intros; try discriminate.
*)
(*
  { apply satisfies_tau_r.
    rewrite (observing_intros _ tree0 (go (observe tree0)) eq_refl).
    apply IHsats; assumption. }
  { injection e_obs1.
*)
Admitted.

Lemma satisfies_eutt_head_spec E A (spec1 spec2:itree_spec E A) tree r :
  eutt_head spec1 spec2 -> paco2 satisfies_ r spec1 tree -> paco2 satisfies_ r spec2 tree.
Proof.
  unfold eutt_head.
  rewrite (observing_intros _ spec1 (go (observe spec1)) eq_refl).
  rewrite (observing_intros _ spec2 (go (observe spec2)) eq_refl).
  set (obs1 := observe spec1). set (obs2 := observe spec2). simpl.
  intros e sats. induction e.
  { rewrite <- REL. assumption. }
  { rewrite <- REL. assumption. }
  { eapply satisfies_vis_spec_funext; eassumption. }
  { apply IHe. rewrite (observing_intros _ (go (observe t1)) t1 eq_refl).
    apply satisfies_inv_tau_l. assumption. }
  { apply satisfies_tau_l.
    rewrite (observing_intros _ t2 (go (observe t2)) eq_refl).
    apply IHe. assumption. }
Qed.


Lemma satisfies_eutt_spec E A (P1 P2:itree_spec E A) tree :
  satisfies P1 tree -> eutt eq P1 P2 -> satisfies P2 tree.
Proof.
  intros 


Admitted.
(*
  revert P1 P2 tree; pcofix CIH; intros P1 P2 tree sats e12.
  destruct (eutt_split _ _ _ _ e12) as [ P1' e1 [ P2' e2 e12' ]].
  eapply satisfies_eutt_head_spec; [ symmetry; eassumption | ].
  assert (satisfies P1' tree) as sats';
    [ eapply satisfies_eutt_head_spec; eassumption | ].
  inversion e12'.
  { rewrite <- (observing_intros _ (Ret r2) _ H). rewrite <- REL.
    rewrite (observing_intros _ (Ret r1) _ H0).
    eapply paco2_mon_bot; [ | intros; eassumption ].
    assumption. }
  { rewrite <- (observing_intros _ (Tau _) _ H).
    rewrite <- (observing_intros _ (Tau _) _ H0) in sats'.

 rewrite <- REL.
    rewrite (observing_intros _ (Ret r1) _ H0).
    eapply paco2_mon_bot; [ | intros; eassumption ].
    assumption. }


  punfold sats. unfold satisfies_ in sats.
  remember (observe P1) as obsP1 eqn: e_obsP1 in sats.
  (* remember (observe P2) as obsP2 eqn: e_obsP2 in sats. *)
  remember (observe tree) as obs_tree eqn: e_obs_tree in sats.
  induction sats. Print eqitF.
  { eapply paco2_mon_bot; [ | intros; eassumption ].
    pfold. unfold satisfies_. rewrite <- e_obsP2. rewrite <- REL.
    punfold sats. unfold satisfies_ in sats.
    rewrite <- e_obsP1 in sats. apply sats. }
  { rewrite <- (observing_intros _ (Tau _) _ e_obsP2).
    pclearbot. pfold.
*)
    (*
    simpl in REL. pfold. unfold satisfies_. rewrite <- e_obsP2. apply Satisfies_TauL.




  revert P1 P2 tree; pcofix CIH; intros P1 P2 tree sats e12.
  punfold e12. unfold eqit_ in e12.
  remember (observe P1) as obsP1 eqn: e_obsP1 in e12.
  remember (observe P2) as obsP2 eqn: e_obsP2 in e12.
  induction e12.
  { eapply paco2_mon_bot; [ | intros; eassumption ].
    pfold. unfold satisfies_. rewrite <- e_obsP2. rewrite <- REL.
    punfold sats. unfold satisfies_ in sats.
    rewrite <- e_obsP1 in sats. apply sats. }
  { rewrite <- (observing_intros _ (Tau _) _ e_obsP2).
    pclearbot. pfold.
    (*
    simpl in REL. pfold. unfold satisfies_. rewrite <- e_obsP2. apply Satisfies_TauL.

    unfold eqit_ in e12. induction e12.
    *)
    admit. }
  { rewrite <- (observing_intros _ (Vis _ _) _ e_obsP2).
    pclearbot.


  { rewrite <- (observing_intros _ (Ret _) _ H). rewrite <- REL.
    rewrite (observing_intros _ (Ret _) _ H0).
    eapply paco2_mon_bot; [ apply sats | intros; eassumption ]. }
  { rewrite <- (observing_intros _ (Tau m2) _ H). pfold. constructor. right.
    apply (CIH m1).
    - apply satisfies_inv_tau_l.
      rewrite (observing_intros _ (Tau m1) _ H0). assumption.
    - apply REL. }
  { 



FIXME HERE: old stuff below

Lemma satisfiesF_exists_eqitF E A r (spec':itree_spec' E A) tree'
      (sats:satisfiesF r spec' tree') :
  exists spec, exists tree,
      eqitF eq true true id eq spec' (observe spec) /\
      eqitF eq true true id eq tree' (observe tree) /\
      r spec tree.
Proof.
  induction sats.
  { exists (Ret a); exists (Ret a); split; [ reflexivity | ]; split; [ reflexivity 


FIXME HERE: cull the below

Lemma satisfies_inv_tau_l E A (P:itree_spec E A) m :
  satisfies (Tau P) m -> satisfies P m.
Proof.
  revert P m; pcofix CIH; intros. punfold H0.



  pose (tauP := Tau P). assert (eqP : tauP = Tau P); [ constructor | ].
  rewrite <- eqP in H0. revert eqP. unfold satisfies_ in H0. induction H0.

induction H0; try rewrite eqP in * |- *; try discriminate.
  revert H0; pattern (Tau P); intro tauP.
  induction H0.
  { rewrite <- (observing_intros _ _ _ H1). pclearbot.
    eapply paco2_mon_bot; intros; eassumption. }
  { rewrite <- (observing_intros _ (Tau tree) _ H1). pfold.
    apply Satisfies_TauR. right. apply CIH. pclearbot. unfold satisfies.
    rewrite <- (observing_intros _ _ (Tau P) H). assumption. }
Qed.


(* FIXME: no longer needed...? *)
Lemma observing_spin E A : observing eq (ITree.spin (E:=E) (R:=A)) (Tau ITree.spin).
Proof.
  constructor. reflexivity.
Qed.


Lemma satisfies_spin E A (tree:itree E A) : satisfies ITree.spin tree.
Proof.
  revert tree; pcofix CIH; intros. pfold.
  unfold satisfies_. rewrite observing_spin. constructor.
  right. apply CIH.
Qed.

Lemma satisfies_inv_ret_l E A a (tree:itree E A) :
  satisfies (Ret a) tree -> eutt eq tree (Ret a).
Proof.
  

  revert tree; pcofix CIH; intros tree sats. pinversion sats.
  { pfold. unfold eqit_. rewrite <- H. constructor. reflexivity. }
  { pfold. unfold eqit_. rewrite <- H0. constructor; [ constructor | ]. Print eqitF.
    


rewrite <- (observing_intros _ (Ret a) _ H).

  intro sats. punfold sats. inversion sats. Focus 2.

pinversion sats. Focus 2.

  revert P m; pcofix CIH; intros. punfold H0. inversion H0.
  { rewrite <- (observing_intros _ _ _ H1). pclearbot.
    eapply paco2_mon_bot; intros; eassumption. }
  { rewrite <- (observing_intros _ (Tau tree) _ H1). pfold.
    apply Satisfies_TauR. right. apply CIH. pclearbot. unfold satisfies.
    rewrite <- (observing_intros _ _ (Tau P) H). assumption. }
Qed.
*)


Instance Proper_eutt_satisfies E A : Proper (eutt eq ==> eutt eq ==> iff) (@satisfies E A).
Proof.
Admitted.

Instance Proper_eutt_satisfiesF E A r : Proper (eutt eq ==> eutt eq ==> iff)
                                               (paco2 (@satisfies_ E A) r).
Proof.
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


(* Our event type = errors *)
Inductive CompMEvent : Type -> Type :=
| ErrorEvent : CompMEvent False
.

(* Our computations are sets of ITrees. That is, they are really more like
specifications of computations *)
Definition CompM (A:Type) : Type := itree_spec CompMEvent A.
