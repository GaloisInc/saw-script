From Coq          Require Import Lists.List.
From Coq          Require Import Logic.FunctionalExtensionality.
Import ListNotations.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.

Fixpoint Nat_cases2_match a f1 f2 f3 (x y : nat) : a :=
  match (x, y) with
  | (O,   _)   => f1 y
  | (S x, O)   => f2 x
  | (S x, S y) => f3 x y (Nat_cases2_match a f1 f2 f3 x y)
  end.

Theorem Nat_cases2_match_spec a f1 f2 f3 x y :
  Nat_cases2 a f1 f2 f3 x y = Nat_cases2_match a f1 f2 f3 x y.
Proof.
  revert y.
  induction x; intros y.
  {
    reflexivity.
  }
  {
    destruct y.
    {
      reflexivity.
    }
    {
      simpl.
      now rewrite IHx.
    }
  }
Qed.

Theorem minNat_min a b : minNat a b = min a b.
Proof.
  revert b.
  induction a; intros b.
  {
    reflexivity.
  }
  {
    destruct b; simpl; intuition.
  }
Qed.

Theorem minNat_Succ n : minNat n (Succ n) = n.
Proof.
  unfold minNat.
  rewrite Nat_cases2_match_spec.
  induction n.
  {
    reflexivity.
  }
  {
    unfold Succ in *.
    simpl.
    intuition.
  }
Qed.

Theorem fold_unfold_IRT As Ds D : forall x, foldIRT As Ds D (unfoldIRT As Ds D x) = x.
Proof.
  induction x; simpl; unfold uncurry; f_equal; try easy.
  (* All that remains is the IRT_BVVec case, which requires functional extensionality
     and the fact that genBVVec and atBVVec define an isomorphism *)
  repeat (apply functional_extensionality_dep; intro).
  rewrite at_gen_BVVec; eauto.
Qed.

Theorem unfold_fold_IRT As Ds D : forall u, unfoldIRT As Ds D (foldIRT As Ds D u) = u.
Proof.
  revert Ds; induction D; try destruct u; simpl; f_equal; try easy.
  (* All that remains is the IRT_BVVec case, which requires functional extensionality
     and the fact that genBVVec and atBVVec define an isomorphism *)
  intros; rewrite <- (gen_at_BVVec _ _ _ u).
  f_equal; repeat (apply functional_extensionality_dep; intro); eauto.
Qed.
