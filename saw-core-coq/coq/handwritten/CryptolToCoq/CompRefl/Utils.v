
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
Import ListNotations.

Definition fromSum {A B C} (f : A -> C) (g : B -> C) (x : A + B) : C :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Definition apSumR {A B C} (f : B -> C) : A + B -> A + C :=
  fromSum inl (fun b => inr (f b)).

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
