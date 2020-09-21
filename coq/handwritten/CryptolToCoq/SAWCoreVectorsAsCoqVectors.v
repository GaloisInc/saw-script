From Bits Require Import operations.
From Bits Require Import spec.

From Coq Require Import Lists.List.
From Coq Require        Numbers.NatInt.NZLog.
From Coq Require Import PeanoNat.
From Coq Require Import Strings.String.
From Coq Require Import Vectors.Vector.
From Coq Require Import Bool.Bool.
From Coq Require Import BinNums.

From CryptolToCoq Require Import SAWCoreScaffolding.

From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrnat.
From mathcomp Require Import ssrbool.
From mathcomp Require Import fintype.
From mathcomp Require Import tuple.

From Coq Require Export ZArith.BinIntDef.

Import VectorNotations.

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

Fixpoint foldl_dep (a : Type) (b : Nat -> Type) (n : Nat)
         (f : forall n, b n -> a -> b (S n)) (base : b O) (v : Vec n a) : b n :=
  match v with
  | Vector.nil => base
  | Vector.cons hd _ tl => foldl_dep a (fun n => b (S n)) _ (fun n => f (S n)) (f _ base hd) tl
  end.

Fixpoint tuple_foldl_dep (a : Type) (b : Nat -> Type) (n : Nat)
         (f : forall n, b n -> a -> b (S n)) (base : b O) (t : n .-tuple a) : b n :=
  match n, t with
  | O, _ => base
  | S m, t => let (hd, tl) := (thead t, behead_tuple t)
               in tuple_foldl_dep a (fun n => b (S n)) _ (fun n => f (S n)) (f _ base hd) tl
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

Definition bitvector (n : Nat) : Type := Vector.t bool n.

(* NOTE BITS are stored in reverse order than bitvector *)
Definition bvToBITS {size : nat} : bitvector size -> BITS size
  := foldl_dep bool BITS size (fun _ bs b => joinlsb (bs, b)) nilB.

(* NOTE BITS are stored in reverse order than bitvector *)
Definition bitsToBv {size : nat} : BITS size -> bitvector size
  := tuple_foldl_dep bool bitvector size (fun _ bv b => Vector.cons _ b _ bv) (Vector.nil _).

(* Use this to write decimal number literals of bitvector type, e.g. bvLit 64 3 *)
Definition bvLit (size : Nat) (lit : Z) : bitvector size := bitsToBv (fromZ lit).

Arguments bvLit : simpl never.

(* Use this to write binary number literals of bitvector type, e.g. bvLit_0b"0011" : bitvector 4 *)
Definition bvLit_0b s : bitvector (length s) := bitsToBv (fromBin s).

Arguments bvLit_0b : simpl never.

(* This tactic runs 'compute' on all bitvector literals in the current goal *)
Ltac compute_bvLits :=
  repeat (match goal with
  | |- context bv [ bvLit ?s ?l ] =>
    let bv' := eval compute in (bvLit s l) in
    let new_goal := context bv [ bv' ] in
        change new_goal; unfold SAWCoreScaffolding.true; unfold SAWCoreScaffolding.false
  | |- context bv [ bvLit_0b ?s ] =>
    let bv' := eval compute in (bvLit_0b s) in
    let new_goal := context bv [ bv' ] in
        change new_goal; unfold SAWCoreScaffolding.true; unfold SAWCoreScaffolding.false
  end).

(* Until we have numeral notations for non-inductive types, we use this for printing.
   Note that this doesn't work for parsing, use bvLit or bvLit_0b instead. *)
Notation "0" := Datatypes.false : type_scope.
Notation "1" := Datatypes.true  : type_scope.
Notation "0" := SAWCoreScaffolding.false : type_scope.
Notation "1" := SAWCoreScaffolding.true  : type_scope.
Notation "0b x" := (cons bool x _ (nil bool)) (at level 80) : type_scope.
Notation "0b x y .. z" := (cons bool x _ (cons bool y _ .. (cons bool z _ (nil bool)) ..)) (at level 80) : type_scope.

Definition joinLSB {n} (v : bitvector n) (lsb : bool) : bitvector n.+1 :=
  Vector.shiftin lsb v.

(* NOTE This can cause Coq to stack overflow, avoid it as much as possible! *)
Fixpoint bvNat (size : Nat) (number : Nat) : bitvector size :=
  bitsToBv (fromNat number).
(*   if size is size'.+1 *)
(*   then joinLSB (bvNat size' (number./2)) (odd number) *)
(*   else Vector.nil _ *)
(* . *)

(* Arguments bvNat : simpl never. *)

Definition bvToNatFolder (n : nat) (b : bool) := b + n.*2.

Fixpoint bvToNat (size : Nat) (v : bitvector size) : Nat :=
  Vector.fold_left bvToNatFolder 0 v.

(* This is annoying to implement, so using BITS conversion *)
Definition bvAdd (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := bitsToBv (addB (bvToBITS a) (bvToBITS b)).

(* This is annoying to implement, so using BITS conversion *)
Definition bvSub (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := bitsToBv (subB (bvToBITS a) (bvToBITS b)).

(* This is annoying to implement, so using BITS conversion *)
Definition bvMul (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := bitsToBv (mulB (bvToBITS a) (bvToBITS b)).

(* This is annoying to implement, so using BITS conversion *)
Definition bvNeg (n : nat) (a : bitvector n)
  : bitvector n
  := bitsToBv (invB (bvToBITS a)).

(* FIXME this is not implemented *)
Definition bvUDiv (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := a.
Opaque bvUDiv.

(* FIXME this is not implemented *)
Definition bvURem (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := a.
Opaque bvURem.

(* FIXME this is not implemented *)
Definition bvSDiv (n : nat) (a : bitvector n.+1) (b : bitvector n.+1)
  : bitvector n.+1
  := a.
Opaque bvSDiv.

(* FIXME this is not implemented *)
Definition bvSRem (n : nat) (a : bitvector n.+1) (b : bitvector n.+1)
  : bitvector n.+1
  := a.
Opaque bvSRem.

(* FIXME this is not implemented (base 2 logarithm) *)
Definition bvLg2 (n : nat) (a : bitvector n)
  : bitvector n
  := a.
Opaque bvLg2.

(* FIXME this is not implemented *)
Definition bvSShr (w : nat) (a : bitvector w.+1) (n : nat)
  : bitvector w.+1
  := a.
Opaque bvSShr.

(* FIXME this is not implemented *)
Definition rotateL (n : nat) (A : Type) (v : Vector.t A n) (i : nat)
  : Vector.t A n
  := v.
Opaque rotateL.

(* FIXME this is not implemented *)
Definition rotateR (n : nat) (A : Type) (v : Vector.t A n) (i : nat)
  : Vector.t A n
  := v.
Opaque rotateR.

Fixpoint shiftL (n : nat) (A : Type) (x : A) (v : Vector.t A n) (i : nat)
  : Vector.t A n
  := match i with
     | O => v
     | S i' => Vector.tl (Vector.shiftin x (shiftL n A x v i'))
     end.

Fixpoint shiftR (n : nat) (A : Type) (x : A) (v : Vector.t A n) (i : nat)
  : Vector.t A n
  := match i with
     | O => v
     | S i' => Vector.shiftout (cons _ x _ (shiftL n A x v i'))
     end.

(* This is annoying to implement, so using BITS conversion *)
Definition bvult (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  ltB (bvToBITS a) (bvToBITS b).

Definition bvugt (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  bvult n b a.

(* This is annoying to implement, so using BITS conversion *)
Definition bvule (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  leB (bvToBITS a) (bvToBITS b).

Definition bvuge (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  bvule n b a.

Definition sign {n : nat} (a : bitvector n) : Bool :=
  match a with
  | Vector.nil => false
  | Vector.cons b _ _ => b
  end.

Definition bvslt (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  let c := bvSub n a b
   in (sign a && ~~ sign b) || (sign a && sign c) || (~~ sign b && sign c).

Definition bvsgt (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  bvslt n b a.

Definition bvsle (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  bvslt n a b || (Vector.eqb _ eqb a b).

Definition bvsge (n : nat) (a : bitvector n) (b : bitvector n) : Bool :=
  bvsle n b a.

(* Axiom intToBv : forall (n : Nat), Integer -> bitvector n. *)

(* Axiom bvToInt : forall (n : Nat), bitvector n -> Integer. *)
