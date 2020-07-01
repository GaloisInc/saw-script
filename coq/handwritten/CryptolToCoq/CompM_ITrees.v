(***
 *** A version of the computation monad using the option-set monad
 ***)

From Coq Require Export Morphisms Setoid.
From ITree Require Export ITree ITreeFacts.

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

CoInductive itree_satisfies_spec {E A} : itree_spec E A -> itree E A -> Prop :=
| Satisfies_Ret a : itree_satisfies_spec (Ret a) (Ret a)
| Satisfies_TauL spec tree :
    itree_satisfies_spec spec tree -> itree_satisfies_spec (Tau spec) tree
| Satisfies_TauR spec tree :
    itree_satisfies_spec spec tree -> itree_satisfies_spec spec (Tau tree)
| Satisfies_Vis X (e:E X) spec tree :
    (forall x, itree_satisfies_spec (spec x) (tree x)) ->
    itree_satisfies_spec (Vis (Spec_vis e) spec) (Vis e tree)
| Satisfies_Forall X spec tree :
    (forall x:X, itree_satisfies_spec (spec x) tree) ->
    itree_satisfies_spec (Vis Spec_forall spec) tree
| Satisfies_Exists X spec tree :
    (exists x:X, itree_satisfies_spec (spec x) tree) ->
    itree_satisfies_spec (Vis Spec_exists spec) tree
.

(* The proposition that a is returned by an itree along some path *)
Inductive is_itree_retval {E A} : itree E A -> A -> Prop :=
| iirv_ret a : is_itree_retval (Ret a) a
| iirv_tau itree a : is_itree_retval itree a -> is_itree_retval (Tau itree) a
| iirv_vis {X} (ev:E X) itree a x : is_itree_retval (itree x) a ->
                                    is_itree_retval (Vis ev itree) a
.

Infix ">>=" := ITree.bind (at level 58, left associativity).
Notation "m1 >> m2" := (m1 >>= fun _ => m2) (at level 58, left associativity).

CoFixpoint itree_satisfies_untau_l' E A spec tree
           (sats:@itree_satisfies_spec E A spec tree) :
  forall spec', spec = Tau spec' -> itree_satisfies_spec spec' tree.
Proof.
  destruct sats; intros; try discriminate.
  - injection H; intro e; rewrite <- e. assumption.
  - apply Satisfies_TauR. apply (itree_satisfies_untau_l' _ _ spec); assumption.
Qed.

Lemma itree_satisfies_untau_l E A spec tree :
  @itree_satisfies_spec E A (Tau spec) tree ->
  itree_satisfies_spec spec tree.
Proof.
  intros sats. apply (itree_satisfies_untau_l' E A _ _ sats _ eq_refl).
Qed.

CoFixpoint itree_satisfies_untau_r' E A spec tree
           (sats:@itree_satisfies_spec E A spec tree) :
  forall tree', tree = Tau tree' -> itree_satisfies_spec spec tree'.
Proof.
  destruct sats; intros; try discriminate.
  - apply Satisfies_TauL. apply (itree_satisfies_untau_r' _ _ _ tree); assumption.
  - injection H; intro e; rewrite <- e. assumption.
  - apply Satisfies_Forall; intro.
    apply (itree_satisfies_untau_r' _ _ _ tree (H x) _ H0).
  - destruct H as [ x H ]. apply Satisfies_Exists. exists x.
    apply (itree_satisfies_untau_r' _ _ _ tree H _ H0).
Qed.

Lemma itree_satisfies_untau_r E A spec tree :
  @itree_satisfies_spec E A spec (Tau tree) ->
  itree_satisfies_spec spec tree.
Proof.
  intros sats. apply (itree_satisfies_untau_r' E A _ _ sats _ eq_refl).
Qed.

CoFixpoint itree_satisfies_eutt_l E A spec tree
           (sats:@itree_satisfies_spec E A spec tree)
           spec' (e:eutt eq spec spec') :
  itree_satisfies_spec spec' tree.
Proof.
Admitted.

CoFixpoint itree_satisfies_eutt_r E A spec tree
           (sats:@itree_satisfies_spec E A spec tree)
           tree' (e:eutt eq tree tree') :
  itree_satisfies_spec spec tree'.
Proof.
Admitted.

Instance Proper_eq_itree_itree_satisfies_spec_impl E A :
  Proper (eutt eq ==> eutt eq ==> iff) (@itree_satisfies_spec E A).
Proof.
  intros spec1 spec2 e_spec tree1 tree2 e_tree.
  split; intro H.
  - eapply itree_satisfies_eutt_l; [ | eassumption ].
    eapply itree_satisfies_eutt_r; [ | eassumption ].
    assumption.
  - eapply itree_satisfies_eutt_l; [ | symmetry; eassumption ].
    eapply itree_satisfies_eutt_r; [ | symmetry; eassumption ].
    assumption.
Qed.


Lemma bind_vis_eutt E A B C (e:E A) (tree:A -> itree E B) (f:B -> itree E C) :
  eutt eq (Vis e tree >>= f) (Vis e (fun x => tree x >>= f)).
Proof.
Admitted.

Lemma bind_satisfies_bind E A B (P:itree_spec E A) (Q:A -> itree_spec E B)
      (m:itree E A) (f:A -> itree E B) :
  itree_satisfies_spec P m ->
  (forall a, is_itree_retval m a -> itree_satisfies_spec (Q a) (f a)) ->
  itree_satisfies_spec (P >>= Q) (m >>= f).
Proof.
  intro sats; revert P m sats B Q f. cofix CIH. intros P m sats; destruct sats; intros.
  { rewrite bind_ret_l. rewrite bind_ret_l. apply H. constructor. }
  { rewrite tau_eutt. apply CIH; assumption. }
  { rewrite tau_eutt. apply CIH; [ assumption | ].
    intros a iirv; apply H. apply iirv_tau; assumption. }
  { rewrite bind_vis_eutt. rewrite bind_vis_eutt.
    apply Satisfies_Vis. intro.
    apply CIH; [ apply H | ]. intros a iirv. apply H0.
    apply (iirv_vis _ _ _ x). assumption. }


FIXME HERE: keep going...



(* Our event type = errors *)
Inductive CompMEvent : Type -> Type :=
| ErrorEvent : CompMEvent False
.

(* Our computations are sets of ITrees. That is, they are really more like
specifications of computations *)
Definition CompM (A:Type) : Type := itree CompMEvent A -> Prop.

