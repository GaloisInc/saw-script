From Stdlib.Lists          Require Import List.
From Stdlib.Numbers.NatInt Require        NZLog.
From Stdlib.Strings        Require        String.
From CryptolToCoq          Require Import SAWCoreScaffolding.
From Stdlib                Require Import ZifyClasses.

Import ListNotations.

Definition Vec (n : nat) (a : Type) : Type := list a.

(* Work around https://github.com/coq/coq/issues/16803. Without this, using
   `lia` on `bitvector` values will fail to typecheck on pre-8.17 versions of
   Coq. Once our Coq support window shifts enough, we can drop this workaround.
*)
Constraint Vec.u1 <= mkapp2.u0.
Constraint Vec.u1 <= mkapp2.u1.
Constraint Vec.u1 <= mkapp2.u2.
Constraint Vec.u1 <= mkrel.u0.
Constraint Vec.u1 <= mkapp.u0.
Constraint Vec.u1 <= mkapp.u1.

Fixpoint gen (n : nat) (a : Type) (f : nat -> a) {struct n} : Vec n a.
  refine (
      match n with
      | O   => []
      | S n' =>  f O :: gen n' _ (fun n => f (S n))
      end
    ).
Defined.

Fixpoint atWithDefault (n : nat) (a : Type) (default : a) (v : Vec n a) (index : nat) : a.
  refine (
      match n with
      | O => default
      | S n' =>
        match v with
        | [] => default
        | h :: t =>
          match index with
          | O => h
          | S index' => atWithDefault n' _ default t index'
          end
        end
      end
  ).
Defined.

Definition map (a b : Type) (f : a -> b) (n : Nat) (xs : Vec n a) :=
  map f xs.

Fixpoint foldr (a b : Type) (n : Nat) (f : a -> b -> b) (base : b) (v : Vec n a) : b :=
  match n with
  | O => base
  | S n' =>
    match v with
    | [] => base
    | hd :: tl => f hd (foldr _ _ n' f base tl)
    end
  end.

(* Definition atWithDefault := VectorExtra.atWithDefault. *)
Definition EmptyVec := @nil.
(* Definition gen := VectorExtra.gen. *)

Definition coerceVec (a : sort 0) (m n : Nat) (eq : Eq Nat m n) (v : Vec m a) : Vec n a :=
  match
    eq_sym eq in eq _ n'
    return Vec n' a -> Vec n a
  with
  | eq_refl _ => fun x => x
  end v.

Theorem gen_add m n T : forall f, gen (m + n) T f = gen m T f ++ gen n T (fun x => f (m + x)).
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

Fixpoint zipFunctional (a b : sort 0) (m n : Nat) (xs : Vec m a) (ys : Vec n b)
  : Vec (Nat.min m n) (a * b) :=
  match (m, n) with
  | (S m', S n') =>
    match (xs, ys) with
    | (x :: xs, y :: ys) => (x, y) :: zipFunctional _ _ m' n' xs ys
    | _ => []
    end
  | _ => []
  end.

Definition zipWithFunctional (a b c : Type) (f : a -> b -> c) (n : Nat) (xs : Vec n a) (ys : Vec n b) :=
  map _ _ (fun p => f (fst p) (snd p)) n (zipFunctional _ _ _ _ xs ys).
