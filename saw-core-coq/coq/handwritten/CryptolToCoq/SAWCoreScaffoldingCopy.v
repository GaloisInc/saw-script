From Stdlib Require Import Lists.List.
From Stdlib Require Import Numbers.NatInt.NZLog.
From Stdlib Require Import Strings.String.

From Ornamental Require Import Ornaments.

Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)

Module SCS.

  Definition sort (n : nat) := Type.

End SCS.

Preprocess Module SCS as SCS'.

  (* Axiom error : forall (a : Type), String.string -> a. *)

  Definition String := String.string.

  Definition Unit        := tt.
  Definition UnitType    := unit.
  Definition UnitType__rec := unit_rect.

  Definition Bool   := bool.
  Definition Eq     := identity.
  Definition Eq__rec  := identity_rect.
  Definition Refl   := identity_refl.
  Definition True      := true.
  Definition ite (a : Type) (b : Bool) (t e : a) : a := if b then t else e.
  Definition and    := andb.
  Definition False      := false.
  Definition not      := negb.
  Definition or     := orb.
  Definition xor    := xorb.
  Definition boolEq := Stdlib.Bool.Bool.eqb.
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
(* NOTE: SAW core prelude's eq is not being used much by the translation at the *)
 (* moment, so we skip it.  The following type class declaration could be used if *)
 (* one wanted to translate `eq`.  However, it would require more work in the *)
 (* translation, because calls to `eq T a b` in SAW must be translated to either `eq *)
 (* a b` or `@eq T _ a b`, where the underscore stands for the dictionary.  As a *)
 (* result, this would not be an identifier-to-identifier translation, but rather a *)
 (* term-to-term translation, and would require knowing the number of arguments *)
 (* expected before the dicitonary. *)
(* *)
 (* Class eqClass `(a : Type) := *)
 (*   { *)
 (*     eq : a -> a -> bool; *)
 (*     eq_refl : forall (x : a), Eq Bool (eq x x) True; *)
 (*   }. *)

 (* Global Instance eqClassBool : eqClass Bool := *)
 (*   { *)
 (*     eq := boolEq; *)
 (*   }. *)
 (* + destruct x; reflexivity. *)
 (* Defined. *)

 (* Theorem eq_Bool : Eq (Bool -> Bool -> Bool) eq boolEq. *)
 (* Proof. *)
 (*   reflexivity. *)
 (* Qed. *)

 (* Global Instance eqClass_sawVec (n : nat) (a : Type) `(A : eqClass a) : eqClass (sawVec n a) := *)
 (*   { *)
 (*     eq := Vector.eqb _ eq; *)
 (*   }. *)
 (* + induction 0 as [|? ? ? IH]. *)
 (*   - reflexivity. *)
 (*   - simpl. *)
 (*     rewrite eq_refl. *)
 (*     rewrite IH. *)
 (*     reflexivity. *)
 (* Defined. *)
 (* *)

(* SAW's prelude defines iteDep as a Bool eliminator whose arguments are *)
 (* reordered to look more like if-then-else. *)
  Definition iteDep (P : Bool -> Type) (b : Bool) : P True -> P False -> P b :=
    fun PTrue PFalse => bool_rect P PTrue PFalse b.

  Definition ite_eq_iteDep : forall (a : Type) (b : Bool) (x y : a),
      @identity a (ite a b x y) (iteDep (fun _ => a) b x y).
  Proof.
    reflexivity.
  Defined.

  Definition iteDep_True : forall (p : Bool -> Type), forall (f1 : p True), forall (f2 : p False), (@identity (p True) (iteDep p True f1 f2)) f1.
  Proof.
    reflexivity.
  Defined.

  Definition iteDep_False : forall (p : Bool -> Type), forall (f1 : p True), forall (f2 : p False), (@identity (p False) (iteDep p False f1 f2)) f2.
  Proof.
    reflexivity.
  Defined.

  Definition not__eq (b : Bool) : @identity Bool (not b) (ite Bool b False True).
  Proof.
    reflexivity.
  Defined.

  Definition and__eq (b1 b2 : Bool) : @identity Bool (and b1 b2) (ite Bool b1 b2 False).
  Proof.
    reflexivity.
  Defined.

  Definition or__eq (b1 b2 : Bool) : @identity Bool (or b1 b2) (ite Bool b1 True b2).
  Proof.
    reflexivity.
  Defined.

  Definition xor__eq (b1 b2 : Bool) : @identity Bool (xor b1 b2) (ite Bool b1 (not b2) b2).
  Proof.
    destruct b1; destruct b2; reflexivity.
  Defined.

(* *)
 (* Definition eq__eq (b1 b2 : Bool) : @identity Bool (eq b1 b2) (ite Bool b1 b2 (not b2)). *)
 (* Proof. *)
 (*   destruct b1; destruct b2; reflexivity. *)
 (* Defined. *)
 (* *)

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

End SCS.

Preprocess Module SCS as SCS'.
