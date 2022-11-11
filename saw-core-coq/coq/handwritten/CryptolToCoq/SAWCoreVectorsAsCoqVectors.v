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
From Coq Require Export PArith.BinPos.

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

Instance Inhabited_Vec (n:nat) (a:Type) {Ha:Inhabited a} : Inhabited (Vec n a) :=
  MkInhabited (Vec n a) (gen n a (fun _ => inhabitant)).

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

Fixpoint foldl (a b : Type) (n : Nat) (f : b -> a -> b) (acc : b) (v : Vec n a) : b :=
  match v with
  | Vector.nil => acc
  | Vector.cons hd _ tl => foldl _ _ _ f (f acc hd) tl
  end.

Fixpoint scanl (a b : Type) (n : Nat) (f : b -> a -> b) (acc : b) (v : Vec n a) : Vec (S n) b :=
  match v in VectorDef.t _ n return Vec (S n) b with
  | Vector.nil => [ acc ]
  | Vector.cons h n' tl => Vector.cons b acc (S n') (scanl a b n' f (f acc h) tl)
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

Definition coerceVec (a : sort 0) (m n : Nat) (H : m = n) (v : Vec m a) : Vec n a :=
  match
    eq_sym H in eq _ n'
    return Vec n' a -> Vec n a
  with
  | eq_refl => fun x => x
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

Notation bitvector n := (Vec n bool).

(* NOTE BITS are stored in reverse order than bitvector *)
Definition bvToBITS {size : nat} : bitvector size -> BITS size
  := foldl_dep bool BITS size (fun _ bs b => joinlsb (bs, b)) nilB.

Arguments bvToBITS : simpl never.

(* NOTE BITS are stored in reverse order than bitvector *)
Definition bitsToBv {size : nat} : BITS size -> bitvector size
  := tuple_foldl_dep bool (fun n => bitvector n) size (fun _ bv b => Vector.cons _ b _ bv) (Vector.nil _).

Arguments bitsToBv : simpl never.

Definition joinLSB {n} (v : bitvector n) (lsb : bool) : bitvector n.+1 :=
  Vector.shiftin lsb v.

Definition bvToNatFolder (n : nat) (b : bool) := b + n.*2.

Definition bvToNat (size : Nat) (v : bitvector size) : Nat :=
  Vector.fold_left bvToNatFolder 0 v.

(* This is used to write literals of bitvector type, e.g. intToBv 64 3 *)
Definition intToBv (n : Nat) (z : Z) : bitvector n := bitsToBv (fromZ z).

Arguments intToBv : simpl never.

(* NOTE This can cause Coq to stack overflow, avoid it as much as possible! *)
Definition bvNat (size : Nat) (number : Nat) : bitvector size :=
  intToBv size (Z.of_nat number).

Arguments bvNat /.

Definition bvToInt (n : Nat) (b : bitvector n) : Z := toPosZ (bvToBITS b).

Definition sbvToInt (n : Nat) (b : bitvector n) : Z
  := match n, b with
     | O, _ => 0
     | S n, b => toZ (bvToBITS b)
     end.

(* Useful notation for bools *)
Definition boolToInt (b : bool) : Z := if b then 1%Z else 0%Z.
Numeral Notation bool Z.odd boolToInt : bool_scope.
Close Scope bool_scope. (* no, don't interpret all numbers as booleans... *)

(* This is annoying to implement, so using BITS conversion *)
Definition bvAdd (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := bitsToBv (addB (bvToBITS a) (bvToBITS b)).
Global Opaque bvAdd.

(* This is annoying to implement, so using BITS conversion *)
Definition bvSub (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := bitsToBv (subB (bvToBITS a) (bvToBITS b)).
Global Opaque bvSub.

(* This is annoying to implement, so using BITS conversion *)
Definition bvMul (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := bitsToBv (mulB (bvToBITS a) (bvToBITS b)).
Global Opaque bvMul.

(* This is annoying to implement, so use bvSub *)
Definition bvNeg (n : nat) (a : bitvector n)
  : bitvector n
  := bvSub n (intToBv n 0) a.

Definition bvUDiv (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := intToBv n (Z.div (bvToInt n a) (bvToInt n b)).
Global Opaque bvUDiv.

Definition bvURem (n : nat) (a : bitvector n) (b : bitvector n)
  : bitvector n
  := intToBv n (Z.modulo (bvToInt n a) (bvToInt n b)).
Global Opaque bvURem.

Definition  bvSDiv (n : nat) (a : bitvector n.+1) (b : bitvector n.+1)
  : bitvector n.+1
  := intToBv (n.+1) (Z.quot (sbvToInt (n.+1) a) (sbvToInt (n.+1) b)).
Global Opaque bvSDiv.

Definition bvSRem (n : nat) (a : bitvector n.+1) (b : bitvector n.+1)
  : bitvector n.+1
  := intToBv (n.+1) (Z.rem (sbvToInt (n.+1) a) (sbvToInt (n.+1) b)).
Global Opaque bvSRem.

Section log2_up.
  (* TODO, really should prove something about this *)
  Definition log2_up z : Z :=
  match z with
  | Z.pos 1 => 0
  | Z.pos p => Z.add (Z.log2 (Z.pos (Pos.pred p))) 1
  | _ => 0
  end.
End log2_up.

Definition bvLg2 (n : nat) (a : bitvector n)
  : bitvector n
  := intToBv n (log2_up (bvToInt n a)).
Global Opaque bvLg2.

Definition bvSShr (w : nat) (a : bitvector w.+1) (n : nat)
  : bitvector w.+1
  := bitsToBv (iter n sarB (bvToBITS a)).
Global Opaque bvSShr.

Definition bvShl (w : nat) (a : bitvector w) (n : nat)
  : bitvector w
  := bitsToBv (shlBn (bvToBITS a) n).
Global Opaque bvShl.

Definition bvShr (w : nat) (a : bitvector w) (n : nat)
  : bitvector w
  := bitsToBv (shrBn (bvToBITS a) n).
Global Opaque bvShr.


(* left shift by one element, shifting in the value of x on the right *)
Definition shiftL1 (n:nat) (A:Type) (x:A) (v : Vector.t A n) :=
  Vector.tl (Vector.shiftin x v).

(* right shift by one element, shifting in the value of x on the left *)
Definition shiftR1 (n:nat) (A:Type) (x:A) (v : Vector.t A n) :=
  Vector.shiftout (cons _ x _ v).

Definition rotateL (n : nat) : forall (A : Type) (v : Vector.t A n) (i : nat), Vector.t A n :=
  match n with
  | O => fun A v i => v
  | S n' => fun A v i => iter i (fun v' => shiftL1 (S n') A (Vector.hd v') v') v
  end.

Definition rotateR (n : nat) : forall (A : Type) (v : Vector.t A n) (i : nat), Vector.t A n :=
  match n with
  | O => fun A v i => v
  | S n' => fun A v i => iter i (fun v' => shiftR1 (S n') A (Vector.last v') v') v
  end.

Definition shiftL (n : nat) (A : Type) (x : A) (v : Vector.t A n) (i : nat) : Vector.t A n :=
  iter i (shiftL1 n A x) v.

Definition shiftR (n : nat) (A : Type) (x : A) (v : Vector.t A n) (i : nat) : Vector.t A n :=
  iter i (shiftR1 n A x) v.

(* This is annoying to implement, so using BITS conversion *)
Definition bvult (n : nat) (a : bitvector n) (b : bitvector n) : bool :=
  ltB (bvToBITS a) (bvToBITS b).
Global Opaque bvult.

Definition bvugt (n : nat) (a : bitvector n) (b : bitvector n) : bool :=
  bvult n b a.

(* This is annoying to implement, so using BITS conversion *)
Definition bvule (n : nat) (a : bitvector n) (b : bitvector n) : bool :=
  leB (bvToBITS a) (bvToBITS b).
Global Opaque bvule.

Definition bvuge (n : nat) (a : bitvector n) (b : bitvector n) : bool :=
  bvule n b a.

Definition sign {n : nat} (a : bitvector n) : bool :=
  match a with
  | Vector.nil => false
  | Vector.cons b _ _ => b
  end.

Definition bvslt (n : nat) (a : bitvector n) (b : bitvector n) : bool :=
  let c := bvSub n a b
   in ((sign a && ~~ sign b) || (sign a && sign c) || (~~ sign b && sign c))%bool.
      (* ^ equivalent to: boolEq (bvSBorrow s a b) (sign (bvSub n a b))  *)
Global Opaque bvslt.

Definition bvsgt (n : nat) (a : bitvector n) (b : bitvector n) : bool :=
  bvslt n b a.

Definition bvsle (n : nat) (a : bitvector n) (b : bitvector n) : bool :=
  (bvslt n a b || (Vector.eqb _ eqb a b))%bool.
Global Opaque bvsle.

Definition bvsge (n : nat) (a : bitvector n) (b : bitvector n) : bool :=
  bvsle n b a.

Definition bvAddOverflow n (a : bitvector n) (b : bitvector n) : bool :=
  let c := bvAdd n a b
   in ((sign a && sign b && ~~ sign c) || (~~ sign a && ~~ sign b && sign c))%bool.

Definition bvSubOverflow n (a : bitvector n) (b : bitvector n) : bool :=
  let c := bvSub n a b
   in ((sign a && ~~ sign b && ~~ sign c) || (~~ sign a && sign b && sign c))%bool.
