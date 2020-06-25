(***
 *** A version of the computation monad using the option-set monad
 ***)

From Coq Require Export Morphisms Setoid.
From ITree Require Export ITree ITreeFacts.

(* The set of ITrees monad *)
Definition ITreeSet E A : Type := itree E A -> Prop.


(* Refinement = subset *)
Definition refinesM {E A} (m1 m2:ITreeSet E A) : Prop :=
  forall itree, m1 itree -> m2 itree.

Instance PreOrder_refinesM E A : PreOrder (@refinesM E A).
Proof.
  constructor.
  - repeat intro; assumption.
  - intros m1 m2 m3 R12 R23 itree in_1. apply R23; apply R12; assumption.
Qed.


(* Equality = refinement in both directions *)
Definition eqM {E A} (m1 m2:ITreeSet E A) : Prop :=
  forall itree, m1 itree <-> m2 itree.

Infix "~=" := eqM (at level 70, no associativity).

Instance Equivalence_eqM E A : Equivalence (@eqM E A).
Proof.
  constructor.
  - intros m itree; reflexivity.
  - intros m1 m2 R12 itree; symmetry; apply R12.
  - intros m1 m2 m3 R12 R23 itree.
    transitivity (m2 itree); [ apply R12 | apply R23 ].
Qed.


(* return x = the set containing exactly the itree return x *)
Definition returnM {E A} (a:A) : ITreeSet E A :=
  fun itree => eutt eq itree (Ret a).


(* The proposition that a is returned by an itree along some path *)
CoInductive is_itree_retval {E A} : itree E A -> A -> Prop :=
| iirv_ret a : is_itree_retval (Ret a) a
| iirv_tau itree a : is_itree_retval itree a -> is_itree_retval (Tau itree) a
| iirv_vis {X} (ev:E X) itree a x : is_itree_retval (itree x) a ->
                                    is_itree_retval (Vis ev itree) a
.

Lemma is_itree_retval_eutt E A (itree1: itree E A) a (iirv: is_itree_retval itree1 a) itree2 :
  eutt eq itree1 itree2 -> is_itree_retval itree2 a.
Admitted.

Instance Proper_is_itree_retval E A : Proper (eutt eq ==> eq ==> iff) (@is_itree_retval E A).
Proof.
  intros itree1 itree2 R12 a1 a2 eq_a; rewrite eq_a.
  split; intro iirv;
    apply (is_itree_retval_eutt _ _ _ _ iirv); [ | symmetry ]; assumption.
Qed.

(* m >>= f is the set of all m' >>= f' such that m' is in m and, for all return
values a of m', f' a is in f a *)
Definition bindM {E A B} (m:ITreeSet E A) (f:A -> ITreeSet E B) : ITreeSet E B :=
  fun itree =>
    exists itree_m,
    exists itree_f,
      eutt eq itree (ITree.bind itree_m itree_f) /\
      m itree_m /\ forall a, is_itree_retval itree_m a -> f a (itree_f a).

Infix ">>=" := bindM (at level 58, left associativity).
Notation "m1 >> m2" := (m1 >>= fun _ => m2) (at level 58, left associativity).

(* bindM is Proper w.r.t eqM *)
Instance Proper_bindM E A B : Proper (eqM ==> (pointwise_relation A eqM) ==> eqM)
                                     (@bindM E A B).
Proof.
  intros m1 m2 Rm f1 f2 Rf itree. unfold eqM, refinesM, bindM.
  split; intros [ itree_m [ itree_f [ eq_mf [ in_m in_f ]]]];
    exists itree_m; exists itree_f; split; try assumption; split;
      try (apply Rm; assumption);
      intros; apply Rf; apply in_f; assumption.
Qed.

(* FIXME: bindM is Proper w.r.t. refinement *)

(* The first monad law *)
Theorem returnM_bindM E A B (a:A) (f:A -> ITreeSet E B) : returnM a >>= f ~= f a.
Proof.
  intro itree. unfold bindM. split.
  - intros [ itree_m [ itree_f [ itree_eq [ in_return in_f ]]]].
    unfold returnM in in_return. rewrite in_return in itree_eq.
    rewrite bind_ret_l in itree_eq.


FIXME: eqM needs to expand the sets up to eutt


(* Our event type = errors *)
Inductive CompMEvent : Type -> Type :=
| ErrorEvent : CompMEvent False
.

(* Our computations are sets of ITrees. That is, they are really more like
specifications of computations *)
Definition CompM (A:Type) : Type := itree CompMEvent A -> Prop.

