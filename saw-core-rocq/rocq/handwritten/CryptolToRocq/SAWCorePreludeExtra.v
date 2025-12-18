From Stdlib        Require Import Arith.
From Stdlib        Require Import Lists.List.
From Stdlib        Require Import Logic.Eqdep_dec.
From Stdlib        Require Import Logic.FunctionalExtensionality.
Import ListNotations.
From Stdlib        Require Import String.
#[local] Set Warnings "-stdlib-vector".
From Stdlib        Require Import Vectors.Vector.
#[local] Set Warnings "stdlib-vector".
From CryptolToRocq Require Import SAWCoreBitvectors.
From CryptolToRocq Require Import SAWCoreScaffolding.
From CryptolToRocq Require Import SAWCorePrelude.
From CryptolToRocq Require Import SAWCoreVectorsAsRocqVectors.
Import SAWCorePrelude.


Fixpoint Nat_cases2_match a f1 f2 f3 (x y : nat) : a :=
  match (x, y) with
  | (O,   _)   => f1 y
  | (S x, O)   => f2 x
  | (S x, S y) => f3 x y (Nat_cases2_match a f1 f2 f3 x y)
  end.

Theorem Nat_cases2_match_spec a f1 f2 f3 : forall x y,
  Nat_cases2 a f1 f2 f3 x y = Nat_cases2_match a f1 f2 f3 x y.
Proof.
  induction x; induction y; simpl; congruence.
Defined.

Theorem minNat_min : forall x y, minNat x y = min x y.
Proof.
  induction x; induction y; simpl; auto.
Defined.

Theorem maxNat_max : forall x y, maxNat x y = max x y.
Proof.
  induction x; induction y; simpl; auto.
Defined.

(* NOTE: addNat is now defined as Rocq plus, so this is trivial *)
Theorem addNat_add : forall x y, addNat x y = x + y.
Proof.
  reflexivity.
Defined.

Theorem subNat_sub : forall x y, subNat x y = x - y.
Proof.
  induction x; induction y; simpl; auto.
Defined.

(* NOTE: mulNat is now defined as Rocq mult, so this is trivial *)
Theorem mulNat_mul : forall x y, mulNat x y = x * y.
Proof.
  reflexivity.
Defined.

Definition streamScanl (a b : sort 0) (f : b -> a -> b) (z:b) (xs:Stream a) : Stream b :=
  MkStream b
    (fix strm (n:nat) : b :=
       match n with
       | O => z
       | S n' => f (strm n') (streamGet a xs n')
       end).

Lemma streamScanl_zero a b f z xs : streamGet b (streamScanl a b f z xs) 0 = z.
Proof.
  reflexivity.
Qed.

Lemma streamScanl_succ a b f z xs : forall n,
  streamGet b (streamScanl a b f z xs) (S n) =
  f (streamGet b (streamScanl a b f z xs) n)
    (streamGet a xs n).
Proof.
  intro n. reflexivity.
Qed.

Lemma bvToNat_bvNat (w n : nat) :
  n < 2^w -> bvToNat w (bvNat w n) = n.
Admitted.

Lemma bvToNat_bounds (w : nat) (x : bitvector w) :
  bvToNat w x < 2^w.
Proof.
  holds_for_bits_up_to_3; try repeat constructor.
Qed.
