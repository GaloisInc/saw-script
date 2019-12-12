From Coq Require Import Lists.List.
From Coq Require        Numbers.NatInt.NZLog.
From Coq Require Import PeanoNat.
From Coq Require        Strings.String.
From Coq Require        Vectors.Vector.

From CryptolToCoq Require Import SAWCoreScaffolding.

From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrnat.
From mathcomp Require Import fintype.

Definition Vec (n : nat) (a : Type) : Type := VectorDef.t a n.

Fixpoint gen (n : nat) (a : Type) (f : nat -> a) {struct n} : Vec n a.
  refine (
      match n with
      | O   => Vector.nil _
      | S p => Vector.cons _ (f O) _ (gen _ _ (fun n => f (S n)))
      end
    ).
Defined.

Theorem gen_domain_eq n T : forall f g (domain_eq : forall i, f i = g i),
    gen n T f = gen n T g.
Proof.
  move : n.
  elim => [|n' IH] f g DEQ.
  { reflexivity. }
  {
    simpl.
    f_equal.
    {
      apply DEQ.
    }
    {
      apply IH.
      intuition.
    }
  }
Qed.

Fixpoint genOrdinal (n : nat) (a : Type) {struct n}
  : forall (f : 'I_n -> a), Vec n a.
  refine (
      match n as n' with
      | O   => fun _ => Vector.nil _
      | S p =>
        fun f =>
          Vector.cons
            _
            (f (Ordinal (ltn0Sn _)))
            _
            (genOrdinal _ _ (fun q => f (rshift 1 q)))
      end
    ).
Defined.

Theorem genOrdinal_domain_eq n T : forall f g (domain_eq : forall i, f i = g i),
    genOrdinal n T f = genOrdinal n T g.
Proof.
  move : n.
  elim => [|n' IH] f g DEQ.
  { reflexivity. }
  {
    simpl.
    f_equal.
    {
      apply DEQ.
    }
    {
      apply IH.
      intuition.
    }
  }
Qed.

Fixpoint atWithDefault (n : nat) (a : Type) (default : a) (v : Vec n a) (index : nat) : a.
  refine (
      match v with
      | Vector.nil => default
      | Vector.cons h n' t =>
        match index with
        | O => h
        | S index' => atWithDefault n' _ default t index'
        end
      end
  ).
Defined.

Definition map (a b : Type) (f : a -> b) (n : Nat) (xs : Vec n a) :=
  VectorDef.map f xs.

Fixpoint foldr (a b : Type) (n : Nat) (f : a -> b -> b) (base : b) (v : Vec n a) : b :=
  match v with
  | Vector.nil => base
  | Vector.cons hd _ tl => f hd (foldr _ _ _ f base tl)
  end.

Definition EmptyVec := Vector.nil.

Definition coerceVec (a : sort 0) (m n : Nat) (eq : Eq Nat m n) (v : Vec m a) : Vec n a :=
  match
    identity_sym eq in identity _ n'
    return Vec n' a -> Vec n a
  with
  | identity_refl => fun x => x
  end v.

Theorem gen_add m n T : forall f, gen (m + n) T f = Vector.append (gen m T f) (gen n T (fun x => f (m + x))).
Proof.
  induction m; intros.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    f_equal.
    now rewrite IHm.
  }
Qed.

(* NOTE: This version of `zip` accepts two vectors of different size, unlike the
 * one in `CoqVectorsExtra.v` *)
Fixpoint zipFunctional (a b : sort 0) (m n : Nat) (xs : Vec m a) (ys : Vec n b)
  : Vec (Nat.min m n) (a * b) :=
  match
    xs in Vector.t _ m'
    return Vector.t _ (Nat.min m' n)
  with
  | Vector.nil => Vector.nil _
  | Vector.cons x pm xs =>
    match
      ys in Vector.t _ n'
      return Vector.t _ (Nat.min (S pm) n')
    with
    | Vector.nil => Vector.nil _
    | Vector.cons y pm' ys => Vector.cons _ (x, y) _ (zipFunctional _ _ _ _ xs ys)
    end
  end
.

Definition zipWithFunctional
           (a b c : Type) (f : a -> b -> c) (n : Nat) (xs : Vec n a) (ys : Vec n b) :=
  VectorDef.map (fun p => f (fst p) (snd p)) (zipFunctional _ _ _ _ xs ys).

Definition joinLSB {n} (v : Vector.t bool n) (lsb : bool) : Vector.t bool n.+1 :=
  Vector.shiftin lsb v.

Fixpoint bvNat (size : Nat) (number : Nat) : Vector.t bool size :=
  if size is size'.+1
  then joinLSB (bvNat size' (number./2)) (Nat.odd number)
  else Vector.nil _
.

Fixpoint bvToNat (size : Nat) (v : Vector.t bool size) : Nat :=
  Vector.fold_left (fun n (b : bool) => b + n.*2) 0 v.

From Bits Require Import operations.
From Bits Require Import spec.

Definition bvToBITS {size : nat} (v : Vector.t bool size)
  : BITS size
  := fromNat (bvToNat size v).

(* This is annoyingto implement, so using BITS conversion *)
Definition bvAdd (n : nat) (a : Vector.t bool n) (b : Vector.t bool n)
  : Vector.t bool n
  := bvNat _ (toNat (addB (bvToBITS a) (bvToBITS b))).

(* This is annoyingto implement, so using BITS conversion *)
Definition bvSub (n : nat) (a : Vector.t bool n) (b : Vector.t bool n)
  : Vector.t bool n
  := bvNat _ (toNat (subB (bvToBITS a) (bvToBITS b))).

(* This is annoyingto implement, so using BITS conversion *)
Definition bvMul (n : nat) (a : Vector.t bool n) (b : Vector.t bool n)
  : Vector.t bool n
  := bvNat _ (toNat (mulB (bvToBITS a) (bvToBITS b))).

Definition bvult (n : nat) (a : Vector.t bool n) (b : Vector.t bool n) : Bool :=
  ltB (bvToBITS a) (bvToBITS b).

(* FIXME this is incorrect, it is unsigned rather than signed *)
Definition bvslt (n : nat) (a : Vector.t bool n) (b : Vector.t bool n) : Bool :=
  ltB (bvToBITS a) (bvToBITS b).

(* Axiom intToBv : forall (n : Nat), Integer -> bitvector n. *)

(* Axiom bvToInt : forall (n : Nat), bitvector n -> Integer. *)
