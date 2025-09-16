(* This module contains additional definitions that can only be defined after *)
(* the Cryptol prelude has been defined. *)

From Coq          Require Import Lia.
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePreludeExtra.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
Import CryptolPrimitivesForSAWCore.

Import ListNotations.

(** It is annoying to have to wrap natural numbers into [TCNum] to use them at
type [Num], so these coercions will do it for us.
 *)
Coercion TCNum : nat >-> Num.
Definition natToNat (n : nat) : Nat := n.
Coercion natToNat : nat >-> Nat.

Theorem Eq_TCNum a b : a = b -> eq (TCNum a) (TCNum b).
Proof.
  intros EQ.
  apply f_equal.
  apply EQ.
Defined.

Theorem min_nSn n : min n (S n) = n.
Proof.
  induction n; simpl; auto.
Defined.

Theorem min_Snn n : min (S n) n = n.
Proof.
  induction n; simpl; auto.
Defined.

Theorem min_nn n : min n n = n.
Proof.
  induction n; simpl; auto.
Defined.

Ltac solveUnsafeAssertStep :=
  match goal with
  | [ |- context [ Succ ] ] => unfold Succ
  | [ |- context [ addNat _ _ ] ] => rewrite addNat_add
  | [ |- context [ mulNat _ _ ] ] => rewrite mulNat_mul
  | [ |- context [ subNat _ _ ] ] => rewrite subNat_sub
  | [ |- context [ maxNat _ _ ] ] => rewrite maxNat_max
  | [ |- context [ minNat _ _ ] ] => rewrite minNat_min
  | [ n : Num |- _ ] => destruct n
  | [ |- Eq Num (TCNum _) (TCNum _) ] => apply Eq_TCNum
  | [ |- Eq Num _ _ ] => reflexivity
  | [ |- min ?n ?n = _ ] => rewrite (min_nn n)
  | [ |- min ?n (S ?n) = _ ] => rewrite (min_nSn n)
  | [ |- min (S ?n) ?n = _ ] => rewrite (min_Snn n)
  end.

Ltac unfoldLets :=
  repeat
  match goal with
    [ X := _ |- _ ] => progress (cbv delta [X])
  end.

Ltac solveUnsafeAssert :=
  try reflexivity;
  try (unfoldLets;
       repeat (repeat solveUnsafeAssertStep; simpl; try reflexivity; try lia);
       trivial).

Fixpoint iterNat {a : Type} (n : nat) (f : a -> a) : a -> a :=
  match n with
  | O    => fun x => x
  | S n' => fun x => iterNat  n' f (f x) (* TODO: check that this is what iter is supposed to do *)
  end
.

Definition iter {a : Type} (n : Num) (f : a -> a) : a -> a :=
    match n with
    | TCNum n => fun xs => iterNat n f xs
    | TCInf   => fun xs => xs
    end
.
