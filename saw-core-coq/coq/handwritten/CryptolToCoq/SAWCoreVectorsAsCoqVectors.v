From Bits Require spec operations.
#[export] Set Bullet Behavior "Strict Subproofs". (* Bits sets this to "None". *)
(* We explicitly re-define local aliases for the parts of Bits we actually use
   to avoid importing ambiguous coercions.
*)
Notation BITS := spec.BITS (only parsing).
Notation nilB := (tuple.nil_tuple bool) (only parsing).
Definition joinlsb {n} := @spec.joinlsb n.
Definition splitlsb {n} := @spec.splitlsb n.
Definition fromZ {n} := @spec.fromZ n.
Definition toPosZ {n} := @spec.toPosZ n.
Definition toZ {n} := @spec.toZ n.
Definition thead {n} {T} := @tuple.thead T n.
Definition behead_tuple {n} {T} := @tuple.behead_tuple T n.
Definition addB {n} (p1 p2 : BITS n) := snd (operations.adcB false p1 p2).
Definition subB {n} (p1 p2 : BITS n) := snd (operations.sbbB false p1 p2).
Definition mulB {n} := @operations.mulB n.
Definition ltB {n} := @operations.ltB n.
Definition leB {n} := @operations.leB n.
Definition sarB {n} := @operations.sarB n.
Definition shlBn {n} := @operations.shlBn n.
Definition shrBn {n} := @operations.shrBn n.

From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Lists.List.
From Stdlib Require        Numbers.NatInt.NZLog.
From Stdlib Require Import Peano_dec.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Strings.String.
#[local] Set Warnings "-stdlib-vector".
From Stdlib Require Import Vectors.Vector.
#[local] Set Warnings "stdlib-vector".
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import ZifyClasses.

From Stdlib Require Import ZArith.BinIntDef.
From Stdlib Require Import PArith.BinPos.

#[local] Undelimit Scope N_scope.
From CryptolToCoq Require Import SAWCoreScaffolding.

From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrnat.
From mathcomp Require Import ssrbool.
From mathcomp Require Import fintype.
From mathcomp Require Import tuple.

Import VectorNotations.

Definition Vec (n : nat) (a : Type) : Type := VectorDef.t a n.

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

Lemma Vec_0_nil :
  forall (a : Type) (v : Vec 0 a),
  v = [].
Proof.
  intros a v.
  apply (case0 (fun v' => v' = [])).
  reflexivity.
Qed.

Lemma Vec_S_cons :
  forall (n : nat) (a : Type) (v : Vec (S n) a),
  exists (x : a) (xs : Vec n a),
  v = x::xs.
Proof.
  intros n a v.
  apply (caseS (fun n' v' => exists (x : a) (xs : Vec n' a), v' = x::xs)).
  intros x m xs.
  exists x. exists xs.
  reflexivity.
Qed.

Fixpoint gen (n : nat) (a : Type) (f : nat -> a) {struct n} : Vec n a.
  refine (
      match n with
      | O   => Vector.nil _
      | S p => Vector.cons _ (f O) _ (gen _ _ (fun n => f (S n)))
      end
    ).
Defined.

Definition head (n : nat) (a : Type) (v : Vec (S n) a) : a := VectorDef.hd v.
Definition tail (n : nat) (a : Type) (v : Vec (S n) a) : Vec n a := VectorDef.tl v.

Lemma head_gen (n : nat) (a : Type) (f : nat -> a) :
  head n a (gen (Succ n) a f) = f 0.
Proof.
  reflexivity.
Qed.

Lemma tail_gen (n : nat) (a : Type) (f : nat -> a) :
  tail n a (gen (Succ n) a f) = gen n a (fun (i:Nat) => f (Succ i)).
Proof.
  reflexivity.
Qed.

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

Fixpoint atWithProof (n : nat) (a : Type) (v : Vec n a) (i : nat) :
    IsLtNat i n -> a :=
  match i as i', n as n' return Vec n' a -> IsLtNat i' n' -> a with
  | _,   O   => fun _ prf =>
                match Nat.nlt_0_r _ prf with end
  | O,   S y => fun v' prf => Vector.hd v'
  | S x, S y => fun v' prf => atWithProof y a (Vector.tl v') x (le_S_n _ _ prf)
  end v.

Definition map (a b : Type) (f : a -> b) (n : nat) (xs : Vec n a) :=
  VectorDef.map f xs.

Fixpoint foldr (a b : Type) (n : nat) (f : a -> b -> b) (base : b) (v : Vec n a) : b :=
  match v with
  | Vector.nil => base
  | Vector.cons hd _ tl => f hd (foldr _ _ _ f base tl)
  end.

Lemma foldr_nil (a b : Type) (f : a -> b -> b) (base : b) (v : Vec 0 a) :
  foldr a b 0 f base v = base.
Proof.
  rewrite (Vec_0_nil _ v). reflexivity.
Qed.

Lemma foldr_cons (a b : Type) (n : nat) (f : a -> b -> b) (base : b)
  (v : Vec (S n) a) : foldr a b (S n) f base v
  = f (VectorDef.hd v) (foldr a b n f base (VectorDef.tl v)).
Proof.
  destruct (Vec_S_cons _ _ v) as [ x [ xs pf ]].
  rewrite pf. reflexivity.
Qed.


Fixpoint foldl (a b : Type) (n : nat) (f : b -> a -> b) (acc : b) (v : Vec n a) : b :=
  match v with
  | Vector.nil => acc
  | Vector.cons hd _ tl => foldl _ _ _ f (f acc hd) tl
  end.

Lemma foldl_nil (a b : Type) (f : b -> a -> b) (base : b) (v : Vec 0 a) :
  foldl a b 0 f base v = base.
Proof.
  rewrite (Vec_0_nil _ v). reflexivity.
Qed.

Lemma foldl_cons (a b : Type) (n : nat) (f : b -> a -> b) (base : b)
  (v : Vec (S n) a) :
  foldl a b (S n) f base v = foldl a b n f (f base (VectorDef.hd v)) (VectorDef.tl v).
Proof.
  destruct (Vec_S_cons _ _ v) as [ x [ xs pf ]].
  rewrite pf. reflexivity.
Qed.

Fixpoint scanl (a b : Type) (n : nat) (f : b -> a -> b) (acc : b) (v : Vec n a) : Vec (S n) b :=
  match v in VectorDef.t _ n return Vec (S n) b with
  | Vector.nil => [ acc ]
  | Vector.cons h n' tl => Vector.cons b acc (S n') (scanl a b n' f (f acc h) tl)
  end.

Fixpoint foldl_dep (a : Type) (b : nat -> Type) (n : nat)
         (f : forall n, b n -> a -> b (S n)) (base : b O) (v : Vec n a) : b n :=
  match v with
  | Vector.nil => base
  | Vector.cons hd _ tl => foldl_dep a (fun n => b (S n)) _ (fun n => f (S n)) (f _ base hd) tl
  end.

Fixpoint tuple_foldl_dep (a : Type) (b : nat -> Type) (n : nat)
         (f : forall n, b n -> a -> b (S n)) (base : b O) (t : n .-tuple a) : b n :=
  match n, t with
  | O, _ => base
  | S m, t => let (hd, tl) := (thead t, behead_tuple t)
               in tuple_foldl_dep a (fun n => b (S n)) _ (fun n => f (S n)) (f _ base hd) tl
  end.

Definition EmptyVec := Vector.nil.

Definition coerceVec (a : sort 0) (m n : nat) (H : m = n) (v : Vec m a) : Vec n a :=
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

Fixpoint genWithProof (n : nat) (a : Type) :
    (forall (i : nat), IsLtNat i n -> a) -> Vec n a :=
  match n as n' return (forall (i : nat), IsLtNat i n' -> a) -> Vec n' a with
  | O   => fun _ => Vector.nil a
  | S m => fun f => Vector.cons a (f 0 (le_n_S _ _ (le_0_n _)))
                                m (genWithProof m a
                                               (fun i prf => f (S i) (le_n_S _ _ prf)))
  end.

(* NOTE: This version of `zip` accepts two vectors of different size, unlike the
 * one in `CoqVectorsExtra.v` *)
Fixpoint zipFunctional (a b : sort 0) (m n : nat) (xs : Vec m a) (ys : Vec n b)
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
           (a b c : Type) (f : a -> b -> c) (n : nat) (xs : Vec n a) (ys : Vec n b) :=
  VectorDef.map (fun p => f (fst p) (snd p)) (zipFunctional _ _ _ _ xs ys).

Lemma at_gen_Vec :
  forall (n : nat) (a : Type)
         (f : forall i : nat, IsLtNat i n -> a)
         (ix : nat) (pf : IsLtNat ix n),
  atWithProof n a (genWithProof n a f) ix pf = f ix pf.
Proof.
  intros n a f.
  induction n; intros ix pf.
  - destruct (Nat.nlt_0_r ix pf).
  - induction ix.
    + simpl.
      rewrite (le_unique _ _ (le_n_S 0 n (le_0_n n)) pf).
      reflexivity.
    + simpl.
      rewrite IHn.
      rewrite (le_unique _ _ (le_n_S (Succ ix) n (le_S_n (S ix) n pf)) pf).
      reflexivity.
Qed.

Lemma gen_at_Vec :
  forall (n : nat) (a : Type) (x : Vec n a),
  genWithProof n a (atWithProof n a x) = x.
Proof.
  intros n a x.
  induction n.
  - rewrite (Vec_0_nil a x). reflexivity.
  - destruct (Vec_S_cons n a x) as [y [ys Yeq]].
    subst x. simpl.
    rewrite <- (IHn ys) at 1.
    do 2 f_equal.
    extensionality i. extensionality prf.
    rewrite (le_unique _ _ (le_S_n (S i) n (le_n_S (Succ i) n prf)) prf).
    reflexivity.
Qed.

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

Definition bvToNat (size : nat) (v : bitvector size) : nat :=
  Vector.fold_left bvToNatFolder 0 v.

(* This is used to write literals of bitvector type, e.g. intToBv 64 3 *)
Definition intToBv (n : nat) (z : Z) : bitvector n := bitsToBv (fromZ z).

Arguments intToBv : simpl never.

(* NOTE This can cause Coq to stack overflow, avoid it as much as possible! *)
Definition bvNat (size : nat) (number : nat) : bitvector size :=
  intToBv size (Z.of_nat number).

Arguments bvNat /.

Definition bvToInt (n : nat) (b : bitvector n) : Z := toPosZ (bvToBITS b).

Definition sbvToInt (n : nat) (b : bitvector n) : Z
  := match n, b with
     | O, _ => 0
     | S n, b => toZ (bvToBITS b)
     end.

(* Useful notation for bools *)
Definition boolToInt (b : bool) : Z := if b then 1%Z else 0%Z.
Number Notation bool Z.odd boolToInt : bool_scope.
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
  Vector.shiftout (VectorDef.cons _ x _ v).

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
