From Coq Require Import Numbers.Cyclic.ZModulo.ZModulo.
From Coq Require Import ZArith.BinInt.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import Lists.List.
From Coq Require        Numbers.NatInt.NZLog.
From Coq Require Import Strings.String.
From CryptolToCoq Require Export CompM.

Definition sawLet_def A B (x : A) (y : A -> B) := y x.

Global Notation "'sawLet' v ':=' x 'in' y" := (sawLet_def _ _ x (fun v => y))
  (at level 70, v at level 99, right associativity).
Global Notation "'sawLet' v ':' A ':=' x 'in' y" := (sawLet_def A _ x (fun v => y))
  (at level 70, v at level 99, right associativity).

(** A typeclass we use to restrict applications of the "error" axiom
  * to inhabited types. This allows the axiom to be realizable, and
  * prevents us from constructing an inconsistent environment.
  *
  * The basic idea is that typeclass instances will be used to construct
  * the necessary inhabitants at use sites, so instances will be needed
  * for all the types expected to be involved in calls to "error".
  *)
Class Inhabited (a:Type) := MkInhabited { inhabitant : a }.

Axiom error : forall (a : Type) {HI:Inhabited a}, String.string -> a.

Definition error_realizable : forall {a : Type} {HI:Inhabited a}, String.string -> a.
Proof. intros; exact inhabitant. Qed.

Definition sort (n : nat) := Type.

Instance Inhabited_Type : Inhabited Type :=
  MkInhabited Type unit.
Instance Inhabited_sort (n:nat) : Inhabited (sort n) :=
  MkInhabited (sort n) unit.

Instance Inhabited_Intro (a:Type) (b:a -> Type) (Hb: forall x, Inhabited (b x))
  : Inhabited (forall x, b x)
  := MkInhabited (forall x, b x) (fun x => @inhabitant (b x) (Hb x)).

Global Hint Extern 5 (Inhabited ?A) =>
  (apply (@MkInhabited A); intuition (eauto with typeclass_instances inh)) : typeclass_instances.

Definition String := String.string.

Instance Inhabited_String : Inhabited String :=
  MkInhabited String ""%string.
Instance Inhabited_string : Inhabited String.string :=
  MkInhabited String.string ""%string.

Definition equalString (s1 s2: String) : bool :=
  match String.string_dec s1 s2 with
  | left _ => true
  | right _ => false
  end.

Definition appendString : String -> String -> String :=
  String.append.

Definition Unit        := tt.
Definition UnitType    := unit.
Definition UnitType__rec := unit_rect.

Definition Bool   := bool.
Definition Eq     := @eq.
Definition Refl   := @eq_refl.
Definition true      := true.
Definition ite (a : Type) (b : Bool) (t e : a) : a := if b then t else e.
Definition and    := andb.
Definition false      := false.
Definition not      := negb.
Definition or     := orb.
Definition xor    := xorb.
Definition boolEq := Coq.Bool.Bool.eqb.

Instance Inhabited_Unit : Inhabited UnitType :=
  MkInhabited UnitType tt.
Instance Inhabited_Bool : Inhabited Bool :=
  MkInhabited Bool false.

Instance Inhabited_unit : Inhabited unit :=
  MkInhabited unit tt.
Instance Inhabited_bool : Inhabited bool :=
  MkInhabited bool false.

(* SAW uses an alternate form of eq_rect where the motive function P also
depends on the equality proof itself *)
Definition Eq__rec (A : Type) (x : A) (P: forall y, x=y -> Type) (p:P x eq_refl) y (e:x=y) :
  P y e.
  dependent inversion e; assumption.
Defined.

Theorem boolEq__eq (b1 b2:Bool) : Eq Bool (boolEq b1 b2) (ite Bool b1 b2 (not b2)).
Proof.
  destruct b1, b2; reflexivity.
Qed.

Definition coerce (a b : sort 0) (p : Eq (sort 0) a b) (x : a) : b :=
  match p in eq _ a' return a' with
  | eq_refl _ => x
  end
.

(* SAW's prelude defines iteDep as a Bool eliminator whose arguments are
reordered to look more like if-then-else. *)
Definition iteDep (P : Bool -> Type) (b : Bool) : P true -> P false -> P b :=
  fun Ptrue Pfalse => bool_rect P Ptrue Pfalse b.

Definition ite_eq_iteDep : forall (a : Type) (b : Bool) (x y : a),
    @eq a (ite a b x y) (iteDep (fun _ => a) b x y).
Proof.
  reflexivity.
Defined.

Definition iteDep_True : forall (p : Bool -> Type), forall (f1 : p true), forall (f2 : p false), (@eq (p true) (iteDep p true f1 f2)) f1.
Proof.
  reflexivity.
Defined.

Definition iteDep_False : forall (p : Bool -> Type), forall (f1 : p true), forall (f2 : p false), (@eq (p false) (iteDep p false f1 f2)) f2.
Proof.
  reflexivity.
Defined.

Definition not__eq (b : Bool) : @eq Bool (not b) (ite Bool b false true).
Proof.
  reflexivity.
Defined.

Definition and__eq (b1 b2 : Bool) : @eq Bool (and b1 b2) (ite Bool b1 b2 false).
Proof.
  reflexivity.
Defined.

Definition or__eq (b1 b2 : Bool) : @eq Bool (or b1 b2) (ite Bool b1 true b2).
Proof.
  reflexivity.
Defined.

Definition xor__eq (b1 b2 : Bool) : @eq Bool (xor b1 b2) (ite Bool b1 (not b2) b2).
Proof.
  destruct b1; destruct b2; reflexivity.
Defined.

(*
Definition eq__eq (b1 b2 : Bool) : @eq Bool (eq b1 b2) (ite Bool b1 b2 (not b2)).
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

Instance Inhabited_Nat : Inhabited Nat :=
  MkInhabited Nat 0%nat.
Instance Inhabited_nat : Inhabited nat :=
  MkInhabited nat 0%nat.

Global Hint Resolve (0%nat : nat) : inh.
Global Hint Resolve (0%nat : Nat) : inh.

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

Instance Inhabited_Pair (a b:Type) {Ha : Inhabited a} {Hb : Inhabited b} : Inhabited (PairType a b) :=
    MkInhabited (PairType a b) (PairValue a b inhabitant inhabitant).
Instance Inhabited_prod (a b:Type) {Ha : Inhabited a} {Hb : Inhabited b} : Inhabited (prod a b) :=
    MkInhabited (prod a b) (pair inhabitant inhabitant).

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

Instance Inhabited_Intger : Inhabited Integer :=
  MkInhabited Integer 0%Z.
Instance Inhabited_Z : Inhabited Z :=
  MkInhabited Z 0%Z.

Global Hint Resolve (0%Z : Z) : inh.
Global Hint Resolve (0%Z : Integer) : inh.


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

Instance Inhabited_IntMod (n:nat) : Inhabited (IntMod n) :=
  MkInhabited (IntMod n) 0%Z.

(***
 *** A simple typeclass-based implementation of SAW record types
 ***
 *** The idea is to support a projection term recordProj e "field" on an element
 *** e of a record type without having to find "field" in the record type of e,
 *** by using typeclass resolution to find it for us.
 ***)

(* The empty record type *)
Variant RecordTypeNil : Type :=
  RecordNil : RecordTypeNil.

(* A non-empty record type *)
Variant RecordTypeCons (str:String.string) (tp:Type) (rest_tp:Type) : Type :=
  RecordCons (x:tp) (rest:rest_tp) : RecordTypeCons str tp rest_tp.

Arguments RecordTypeCons str%string_scope tp rest_tp.
Arguments RecordCons str%string_scope {tp rest_tp} x rest.

Instance Inhabited_RecordNil : Inhabited RecordTypeNil :=
    MkInhabited RecordTypeNil RecordNil.
Instance Inhabited_RecordCons (fnm:String.string) (tp rest_tp:Type)
  {Htp : Inhabited tp} {Hrest : Inhabited rest_tp}
  : Inhabited (RecordTypeCons fnm tp rest_tp)
  := MkInhabited (RecordTypeCons fnm tp rest_tp) (RecordCons fnm inhabitant inhabitant).

(* Get the head element of a non-empty record type *)
Definition recordHead {str tp rest_tp} (r:RecordTypeCons str tp rest_tp) : tp :=
  match r with
  | RecordCons _ x _ => x
  end.

(* Get the tail of a non-empty record type *)
Definition recordTail {str tp rest_tp} (r:RecordTypeCons str tp rest_tp) : rest_tp :=
  match r with
  | RecordCons _ _ rest => rest
  end.

(* An inductive description of a string being a field in a record type *)
Inductive IsRecordField (str:String) : Type -> Type :=
| IsRecordField_Base tp rtp : IsRecordField str (RecordTypeCons str tp rtp)
| IsRecordField_Step str' tp rtp : IsRecordField str rtp ->
                                   IsRecordField str (RecordTypeCons str' tp rtp).

(* We want to use this as a typeclass, with its constructors for instances *)
Existing Class IsRecordField.
Hint Constructors IsRecordField : typeclass_instances.

(* If str is a field in record type rtp, get its associated type *)
Fixpoint getRecordFieldType rtp str `{irf:IsRecordField str rtp} : Type :=
  match irf with
  | IsRecordField_Base _ tp rtp => tp
  | IsRecordField_Step _ _ _ _ irf' => @getRecordFieldType _ _ irf'
  end.

(* If str is a field in record r of record type rtp, get its associated value *)
Fixpoint getRecordField {rtp} str `{irf:IsRecordField str rtp} :
  rtp -> getRecordFieldType rtp str :=
  match irf in IsRecordField _ rtp
        return rtp -> getRecordFieldType rtp str (irf:=irf) with
  | IsRecordField_Base _ tp rtp' => fun r => recordHead r
  | IsRecordField_Step _ _ _ _ irf' =>
    fun r => @getRecordField _ _ irf' (recordTail r)
  end.

(* Reorder the arguments of getRecordField *)
Definition RecordProj {rtp} (r:rtp) str `{irf:IsRecordField str rtp} :
  getRecordFieldType rtp str :=
  getRecordField str r.

Arguments RecordProj {_} r str%string {_}.


(* Some tests *)

Definition recordTest1 := RecordCons "fld1" 0 (RecordCons "fld2" true RecordNil).
(* Check recordTest1. *)

Definition recordTest2 := RecordProj recordTest1 "fld1".
(* Check recordTest2. *)

(* Definition recordTestFail := RecordProj recordTest1 "fld3". *)

Definition recordTest4 :=
 RecordCons "id_fun" (fun (X:Type) (x:X) => x) RecordNil.

Definition recordTest5 := RecordProj recordTest4 "id_fun" nat 0.
