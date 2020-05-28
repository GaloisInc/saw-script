From Coq Require Import Numbers.Cyclic.ZModulo.ZModulo.
From Coq Require Import ZArith.BinInt.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import Lists.List.
From Coq Require        Numbers.NatInt.NZLog.
From Coq Require        Strings.String.
From CryptolToCoq Require Export CompM.

Definition sort (n : nat) := Type.

Axiom error : forall (a : Type), String.string -> a.

Definition String := String.string.

Definition equalString (s1 s2: String) : bool :=
  match String.string_dec s1 s2 with
  | left _ => true
  | right _ => false
  end.

Definition Unit        := tt.
Definition UnitType    := unit.
Definition UnitType__rec := unit_rect.

Definition Bool   := bool.
Definition Eq     := identity.
Definition Eq__rec  := identity_rect.
Definition Refl   := identity_refl.
Definition EqP     := @eq.
Definition ReflP  := @eq_refl.
Definition true      := true.
Definition ite (a : Type) (b : Bool) (t e : a) : a := if b then t else e.
Definition and    := andb.
Definition false      := false.
Definition not      := negb.
Definition or     := orb.
Definition xor    := xorb.
Definition boolEq := Coq.Bool.Bool.eqb.

(* SAW uses an alternate form of eq_rect where the motive function P also
depends on the equality proof itself *)
Definition EqP__rec (A : Type) (x : A) (P: forall y, x=y -> Type) (p:P x eq_refl) y (e:x=y) :
  P y e.
  dependent inversion e; assumption.
Defined.

Theorem boolEq__eq (b1 b2:Bool) : Eq Bool (boolEq b1 b2) (ite Bool b1 b2 (not b2)).
Proof.
  destruct b1, b2; reflexivity.
Qed.

Definition coerce (a b : sort 0) (eq : Eq (sort 0) a b) (x : a) : b :=
  match eq in identity _ a' return a' with
  | identity_refl _ => x
  end
.

(** Typeclass for `eq` **)
(* NOTE: SAW core prelude's eq is not being used much by the translation at the
moment, so we skip it.  The following type class declaration could be used if
one wanted to translate `eq`.  However, it would require more work in the
translation, because calls to `eq T a b` in SAW must be translated to either `eq
a b` or `@eq T _ a b`, where the underscore stands for the dictionary.  As a
result, this would not be an identifier-to-identifier translation, but rather a
term-to-term translation, and would require knowing the number of arguments
expected before the dicitonary. *)
(*
Class eqClass `(a : Type) :=
  {
    eq : a -> a -> bool;
    eq_refl : forall (x : a), Eq Bool (eq x x) True;
  }.

Global Instance eqClassBool : eqClass Bool :=
  {
    eq := boolEq;
  }.
+ destruct x; reflexivity.
Defined.

Theorem eq_Bool : Eq (Bool -> Bool -> Bool) eq boolEq.
Proof.
  reflexivity.
Qed.

Global Instance eqClass_sawVec (n : nat) (a : Type) `(A : eqClass a) : eqClass (sawVec n a) :=
  {
    eq := Vector.eqb _ eq;
  }.
+ induction 0 as [|? ? ? IH].
  - reflexivity.
  - simpl.
    rewrite eq_refl.
    rewrite IH.
    reflexivity.
Defined.
*)

(* SAW's prelude defines iteDep as a Bool eliminator whose arguments are
reordered to look more like if-then-else. *)
Definition iteDep (P : Bool -> Type) (b : Bool) : P true -> P false -> P b :=
  fun Ptrue Pfalse => bool_rect P Ptrue Pfalse b.

Definition ite_eq_iteDep : forall (a : Type) (b : Bool) (x y : a),
    @identity a (ite a b x y) (iteDep (fun _ => a) b x y).
Proof.
  reflexivity.
Defined.

Definition iteDep_True : forall (p : Bool -> Type), forall (f1 : p true), forall (f2 : p false), (@identity (p true) (iteDep p true f1 f2)) f1.
Proof.
  reflexivity.
Defined.

Definition iteDep_False : forall (p : Bool -> Type), forall (f1 : p true), forall (f2 : p false), (@identity (p false) (iteDep p false f1 f2)) f2.
Proof.
  reflexivity.
Defined.

Definition not__eq (b : Bool) : @identity Bool (not b) (ite Bool b false true).
Proof.
  reflexivity.
Defined.

Definition and__eq (b1 b2 : Bool) : @identity Bool (and b1 b2) (ite Bool b1 b2 false).
Proof.
  reflexivity.
Defined.

Definition or__eq (b1 b2 : Bool) : @identity Bool (or b1 b2) (ite Bool b1 true b2).
Proof.
  reflexivity.
Defined.

Definition xor__eq (b1 b2 : Bool) : @identity Bool (xor b1 b2) (ite Bool b1 (not b2) b2).
Proof.
  destruct b1; destruct b2; reflexivity.
Defined.

(*
Definition eq__eq (b1 b2 : Bool) : @identity Bool (eq b1 b2) (ite Bool b1 b2 (not b2)).
Proof.
  destruct b1; destruct b2; reflexivity.
Defined.
*)

Theorem ite_bit (b c d : Bool) : Eq Bool (ite Bool b c d) (and (or (not b) c) (or b d)).
Proof.
  destruct b, c, d; reflexivity.
Qed.

(* TODO: doesn't actually coerce *)
Definition sawCoerce {T : Type} (a b : Type) (_ : T) (x : a) := x.

(* TODO: doesn't actually coerce *)
Definition sawUnsafeCoerce (a b : Type) (x : a) := x.

Definition Nat := nat.
Definition Nat_rect := nat_rect.

(* Definition minNat := Nat.min. *)

Definition uncurry (a b c : Type) (f : a -> b -> c) (p : a * (b * unit)) : c  :=
  f (fst p) (fst (snd p)).

Definition widthNat (n : Nat) : Nat := 1 + Nat.log2 n.

Definition divModNat (x y : Nat) : (Nat * Nat) :=
  match y with
  | 0 => (y, y)
  | S y'=>
    let (p, q) := Nat.divmod x y' 0 y' in
    (p, y' - q)
  end.

Definition id := @id.
Definition PairType := prod.
Definition PairValue := @pair.
Definition Pair__rec := prod_rect.
Definition fst {A B} := @fst A B.
Definition snd {A B} := @snd A B.
Definition Zero := O.
Definition Succ := S.


Definition Integer := Z.
Definition intAdd : Integer -> Integer -> Integer := Z.add.
Definition intSub : Integer -> Integer -> Integer := Z.sub.
Definition intMul : Integer -> Integer -> Integer := Z.mul.
Definition intDiv : Integer -> Integer -> Integer := Z.div.
Definition intMod : Integer -> Integer -> Integer := Z.modulo.
Definition intMin : Integer -> Integer -> Integer := Z.min.
Definition intMax : Integer -> Integer -> Integer := Z.max.
Definition intNeg : Integer -> Integer := Z.opp.
Definition intAbs : Integer -> Integer := Z.abs.
Definition intEq : Integer -> Integer -> Bool := Z.eqb.
Definition intLe : Integer -> Integer -> Bool := Z.leb.
Definition intLt : Integer -> Integer -> Bool := Z.ltb.
Definition intToNat : Integer -> Nat := Z.to_nat.
Definition natToInt : Nat -> Integer := Z.of_nat.

(* NOTE: the following will be nonsense for values of n <= 1 *)
Definition IntMod (n : nat) := Z.
Definition toIntMod (n : Nat) : Integer -> IntMod n := fun i => Z.modulo i (Z.of_nat n).
Definition fromIntMod (n : Nat) : (IntMod n) -> Integer := ZModulo.to_Z (Pos.of_nat n).
Local Notation "[| a |]_ n" := (to_Z (Pos.of_nat n) a) (at level 0, a at level 99).
Definition intModEq (n : Nat) (a : IntMod n) (b : IntMod n) : Bool
  := Z.eqb [| a |]_n [| b |]_n.
Definition intModAdd : forall (n : Nat), (IntMod n) -> (IntMod n) -> IntMod n
  := fun _ => ZModulo.add.
Definition intModSub : forall (n : Nat), (IntMod n) -> (IntMod n) -> IntMod n
  := fun _ => ZModulo.sub.
Definition intModMul : forall (n : Nat), (IntMod n) -> (IntMod n) -> IntMod n
  := fun _ => ZModulo.mul.
Definition intModNeg : forall (n : Nat), (IntMod n) -> IntMod n
  := fun _ => ZModulo.opp.
