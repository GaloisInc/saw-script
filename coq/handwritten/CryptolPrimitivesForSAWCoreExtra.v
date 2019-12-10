(* This module contains additional definitions that can only be defined after *)
(* the Cryptol prelude has been defined. *)

From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From Records      Require Import Records.
From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePreludeExtra.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
Import CryptolPrimitives.

Import ListNotations.

(** It is annoying to have to wrap natural numbers into [TCNum] to use them at
type [Num], so these coercions will do it for us.
 *)
Coercion TCNum : Nat >-> Num.
Definition natToNat (n : nat) : Nat := n.
Coercion natToNat : nat >-> Nat.

Theorem Eq_TCNum a b : a = b -> Eq _ (TCNum a) (TCNum b).
Proof.
  intros EQ.
  rewrite EQ.
  reflexivity.
Qed.

Theorem min_S n : min n (S n) = n.
Proof.
  rewrite PeanoNat.Nat.min_comm.
  induction n.
  { reflexivity. }
  { simpl in *. intuition. }
Qed.

Ltac solveUnsafeAssertStep :=
  match goal with
  | [ |- context [ Succ ] ] => unfold Succ
  | [ n : Num |- _ ] => destruct n
  | [ |- Eq Num (TCNum _) (TCNum _) ] => apply Eq_TCNum
  | [ |- Eq Num _ _ ] => reflexivity
  | [ |- context [ minNat _ _ ] ] => rewrite minNat_min
  | [ |- min ?n (S ?n) = ?n ] => apply min_S
  end.

Ltac solveUnsafeAssert := repeat (solveUnsafeAssertStep; simpl).

Definition cbc_enc_helper n : Eq Num (tcMin n (tcAdd (TCNum 1) n)) n :=
  ltac:(solveUnsafeAssert).

(*
Goal forall n p b, Eq Num (tcAdd n (tcAdd (TCNum 32) p)) (tcMul (tcAdd (TCNum 2) b) (TCNum 16)).
  intros.
  simpl.
  solve_unsafeAssert_step. simpl.

Goal forall n0, Eq Num TCInf
   (TCNum
      (S
         (S
            (S
               (S
                  (S
                     (S
                        (S
                           (S
                              (S
                                 (S
                                    (S
                                       (S
                                          (S
                                             (S
                                                (S
                                                   (S
                                                      (S
                                                         (S
                                                            (S
                                                               (S
                                                                  (S
                                                                     (S
                                                                        (S
                                                                           (S
                                                                              (S
                                                                                 (S
                                                                                    (S
                                                                                       (S
                                                                                          (S (S (S (S (mulNat n0 16)))))))))))))))))))))))))))))))))).
  intros.
  solve_unsafeAssert.
*)

Fixpoint iterNat {a : Type} (n : nat) (f : a -> a) : a -> a :=
  match n with
  | O    => fun x => x
  | S n' => fun x => iterNat  n' f (f x) (* TODO: check that this is what iter is supposed to do *)
  end
.

Fixpoint iter {a : Type} (n : Num) (f : a -> a) : a -> a :=
    match n with
    | TCNum n => fun xs => iterNat n f xs
    | TCInf   => fun xs => xs
    end
.
