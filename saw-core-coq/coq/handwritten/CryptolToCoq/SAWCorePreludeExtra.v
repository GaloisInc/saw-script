From Coq          Require Import Arith.Peano_dec.
From Coq          Require Import Arith.PeanoNat.
From Coq          Require Import Lists.List.
From Coq          Require Import Logic.Eqdep_dec.
From Coq          Require Import Logic.FunctionalExtensionality.
Import ListNotations.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
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

(* NOTE: addNat is now defined as Coq plus, so this is trivial *)
Theorem addNat_add : forall x y, addNat x y = x + y.
Proof.
  reflexivity.
Defined.

Theorem subNat_sub : forall x y, subNat x y = x - y.
Proof.
  induction x; induction y; simpl; auto.
Defined.

(* NOTE: mulNat is now defined as Coq mult, so this is trivial *)
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

Theorem at_gen_BVVec :
  forall (n : nat) (len : bitvector n) (a : Type)
         (f : forall i : bitvector n, is_bvult n i len -> a)
         (ix : bitvector n) (pf : is_bvult n ix len),
  atBVVec n len a (genBVVec n len a f) ix pf = f ix pf.
Proof.
  intros n len a f ix pf.
  unfold atBVVec, genBVVec.
  rewrite at_gen_Vec.
  generalize (IsLtNat_to_bvult n len (bvToNat n ix)
               (bvult_to_IsLtNat n len (bvToNat n ix)
                 (trans bool (bvult n (bvNat n (bvToNat n ix)) len) (bvult n ix len) 1%bool
                   (eq_cong (bitvector n) (bvNat n (bvToNat n ix)) ix (bvNat_bvToNat n ix) bool
                     (fun y : bitvector n => bvult n y len)) pf))) as pf2.
  rewrite (bvNat_bvToNat n ix).
  intros pf2.
  rewrite (UIP_dec Bool.bool_dec pf2 pf).
  reflexivity.
Qed.

Lemma gen_at_BVVec :
  forall (n : nat) (len : bitvector n) (a : Type) (x : BVVec n len a),
  genBVVec n len a (atBVVec n len a x) = x.
Proof.
  intros n len a x.
  unfold genBVVec, atBVVec.
  rewrite <- (gen_at_Vec _ _ x) at 1.
  f_equal. extensionality i. extensionality pf.
  generalize (bvult_to_IsLtNat n len (bvToNat n (bvNat n i))
               (trans bool (bvult n (bvNat n (bvToNat n (bvNat n i))) len) (bvult n (bvNat n i) len) 1%bool
                 (eq_cong (bitvector n) (bvNat n (bvToNat n (bvNat n i))) (bvNat n i)
                    (bvNat_bvToNat n (bvNat n i)) bool (fun y : bitvector n => bvult n y len))
                 (IsLtNat_to_bvult n len i pf))) as pf2.
  assert (X : bvToNat n (bvNat n i) = i).
  { apply bvToNat_bvNat.
    transitivity (bvToNat n len).
    - exact pf.
    - apply bvToNat_bounds.
  }
  rewrite X. intros pf2.
  rewrite (le_unique _ _ pf2 pf).
  reflexivity.
Qed.
