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

Theorem addNat_add : forall x y, addNat x y = x + y.
Proof.
  induction x; simpl; auto.
Defined.

Theorem subNat_sub : forall x y, subNat x y = x - y.
Proof.
  induction x; induction y; simpl; auto.
Defined.

Theorem mulNat_mul : forall x y, mulNat x y = x * y.
Proof.
  induction x; simpl; intros; auto.
  rewrite IHx.
  apply addNat_add.
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
  revert Ds; induction D; intros; try destruct u; simpl(*; f_equal; try easy*).
  (* For some reason using `f_equal` above generates universe constraints like
     `prod.u0 < eq.u0` which cause problems later on when it is assumed that
     `eq.u0 = Coq.Relations.Relation_Definitions.1 <= prod.u0` by
     `returnM_injective`. The easiest solution is just to not use `f_equal`
     here, and rewrite by the relevant induction hypotheses instead. *)
  all: try rewrite IHD; try rewrite IHD1; try rewrite IHD2; try rewrite H; try easy.
  (* All that remains is the IRT_BVVec case, which requires functional extensionality
     and the fact that genBVVec and atBVVec define an isomorphism *)
  intros; rewrite <- (gen_at_BVVec _ _ _ u).
  f_equal; repeat (apply functional_extensionality_dep; intro); eauto.
Qed.
