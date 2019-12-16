From Coq          Require Import Lists.List.
Import ListNotations.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From Records      Require Import Records.
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
