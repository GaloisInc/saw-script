
From Coq          Require Import Lists.List.
From Coq          Require Import Bool.Bool.
From Coq          Require Import Logic.Eqdep.
From Coq          Require Import Logic.FunctionalExtensionality.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompM.

Import ListNotations.
Import EqNotations.

Definition fromSum {A B C} (f : A -> C) (g : B -> C) (x : A + B) : C :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Definition fmapSumR {A B C} (f : B -> C) : A + B -> A + C :=
  fromSum inl (fun b => inr (f b)).

Definition apSumR {A B C} : A + (B -> C) -> A + B -> A + C :=
  fromSum (fun a _ => inl a) fmapSumR.

Fixpoint mapSumList {A B C} (f : A -> B + C) (l : list A) : B + list C :=
  match l with
  | [] => inr []
  | a :: l => match f a, mapSumList f l with
              | inr c, inr l' => inr (c :: l')
              | inl b, _ => inl b
              | _, inl b => inl b
              end
  end.

Lemma bool_eq_iff_eq_true_impls b1 b2 : b1 = b2 <-> (b1 = true <-> b2 = true).
Proof.
  repeat (split; intros); subst; eauto.
  destruct H, b1; symmetry; eauto.
  destruct b2; symmetry; eauto.
Qed.

Definition eq_dep_eq1 {U P p x q y} (eq : eq_dep U P p x q y) : p = q :=
  match eq with
  | eq_dep_intro => eq_refl
  end.

Lemma f_eq_dep_2 :
  forall U (P Q : U -> Type) R p q x y z w (f : forall p, P p -> Q p -> R p),
    eq_dep U P p x q y -> eq_dep U Q p z q w -> eq_dep U R p (f p x z) q (f q y w).
Proof.
  intros.
  destruct (eq_dep_eq1 H).
  apply eq_dep_eq in H; apply eq_dep_eq in H0.
  destruct H, H0; reflexivity.
Qed.

Lemma eq_dep_fun_ext {U A} {P : U -> Type} {p q} {f : A -> P p} {g : A -> P q} :
  p = q -> (forall x, eq_dep U P p (f x) q (g x)) -> eq_dep U (fun i => A -> P i) p f q g.
Proof.
  destruct 1; intros.
  enough (f = g) by (rewrite H0; eauto).
  apply functional_extensionality; intro.
  specialize (H x).
  apply eq_dep_eq in H; eauto.
Qed.

Lemma eq_dep_bindM {A B C D : Set} {m1 m2} {k1 : A -> CompM C} {k2 : B -> CompM D} :
  forall (H : eq_dep Set CompM A m1 B m2), C = D ->
  (forall a, eq_dep Set CompM C (k1 a) D (k2 (rew eq_dep_eq1 H in a))) ->
  eq_dep Set CompM C (m1 >>= k1) D (m2 >>= k2).
Proof.
  intros.
  destruct (eq_dep_eq1 H); apply eq_dep_eq in H.
  destruct H, H0.
  apply eq_dep_fun_ext in H1; eauto.
  apply eq_dep_eq in H1; simpl in H1.
  rewrite H1; reflexivity.
Qed.
