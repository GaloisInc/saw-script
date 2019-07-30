From Coq.Lists          Require Import List.
From Coq.Numbers.NatInt Require        NZLog.
From Coq                Require Import PeanoNat.
From Coq.Strings        Require        String.
From Coq.Vectors        Require        Vector.
From CryptolToCoq       Require Import SAWCoreScaffolding.

Definition Vec (n : nat) (a : Type) : Type := VectorDef.t a n.

Fixpoint gen (n : nat) (a : Type) (f : nat -> a) {struct n} : Vec n a.
  refine (
      match n with
      | O   => Vector.nil _
      | S p => Vector.cons _ (f O) _ (gen _ _ (fun n => f (S n)))
      end
    ).
Defined.

Fixpoint atWithDefault (n : nat) (a : Type) (default : a) (v : Vec n a) (index : nat) : a.
  refine (
      match v with
      | Vector.nil _ => default
      | Vector.cons _ h n' t =>
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
  | Vector.nil _ => base
  | Vector.cons _ hd _ tl => f hd (foldr _ _ _ f base tl)
  end.

Definition EmptyVec := Vector.nil.

Definition coerceVec (a : sort 0) (m n : Nat) (eq : Eq Nat m n) (v : Vec m a) : Vec n a :=
  match
    identity_sym eq in identity _ n'
    return Vec n' a -> Vec n a
  with
  | identity_refl _ => fun x => x
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
  | Vector.nil _ => Vector.nil _
  | Vector.cons _ x pm xs =>
    match
      ys in Vector.t _ n'
      return Vector.t _ (Nat.min (S pm) n')
    with
    | Vector.nil _ => Vector.nil _
    | Vector.cons _ y pm' ys => Vector.cons _ (x, y) _ (zipFunctional _ _ _ _ xs ys)
    end
  end
.

Definition zipWithFunctional (a b c : Type) (f : a -> b -> c) (n : Nat) (xs : Vec n a) (ys : Vec n b) :=
  VectorDef.map (fun p => f (fst p) (snd p)) (zipFunctional _ _ _ _ xs ys).
