From Coq Require Import Numbers.Cyclic.ZModulo.ZModulo.
From Coq Require Import ZArith.BinInt.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import NArith.NArith.
From Coq Require Import Lists.List.
From Coq Require        Numbers.NatInt.NZLog.
From Coq Require Import Strings.String.
From Coq Require Export Logic.Eqdep.


(***
 *** sawLet
 ***)

Definition sawLet_def A B (x : A) (y : A -> B) := y x.

Global Notation "'sawLet' v ':=' x 'in' y" := (sawLet_def _ _ x (fun v => y))
  (at level 70, v at level 99, right associativity).
Global Notation "'sawLet' v ':' A ':=' x 'in' y" := (sawLet_def A _ x (fun v => y))
  (at level 70, v at level 99, right associativity).


(***
 *** The Inhabited typeclass
 ***)

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

Global Instance Inhabited_Type : Inhabited Type :=
  MkInhabited Type unit.
Global Instance Inhabited_sort (n:nat) : Inhabited (sort n) :=
  MkInhabited (sort n) unit.

Global Instance Inhabited_Intro (a:Type) (b:a -> Type) (Hb: forall x, Inhabited (b x))
  : Inhabited (forall x, b x)
  := MkInhabited (forall x, b x) (fun x => @inhabitant (b x) (Hb x)).

Global Hint Extern 5 (Inhabited ?A) =>
  (apply (@MkInhabited A); intuition (eauto with typeclass_instances inh)) : typeclass_instances.


(***
 *** Definitions for things in the Prelude
 ***)

(** DEPRECATED: Use [string] instead. *)
Definition String := String.string.

Global Instance Inhabited_String : Inhabited String :=
  MkInhabited String ""%string.
Global Instance Inhabited_string : Inhabited String.string :=
  MkInhabited String.string ""%string.

Definition equalString (s1 s2: string) : bool :=
  match String.string_dec s1 s2 with
  | left _ => true
  | right _ => false
  end.

Definition appendString : string -> string -> string :=
  String.append.

Definition Unit        := tt.
Definition UnitType    := unit.
Definition UnitType__rec := unit_rect.

(** DEPRECATED: Use [bool] instead. *)
Definition Bool   := bool.

(** DEPRECATED: Use [eq] instead. *)
Definition Eq     := @eq.

(** DEPRECATED: Use [eq_refl] instead. *)
Definition Refl   := @eq_refl.

Definition ite (a : Type) (b : Bool) (t e : a) : a := if b then t else e.

(** DEPRECATED: Use [andb] instead. *)
Definition and    := andb.

(** DEPRECATED: Use [negb] instead. *)
Definition not      := negb.

(** DEPRECATED: Use [orb] instead. *)
Definition or     := orb.

(** DEPRECATED: Use [xorb] instead. *)
Definition xor    := xorb.

Definition boolEq := Coq.Bool.Bool.eqb.

Global Instance Inhabited_Unit : Inhabited UnitType :=
  MkInhabited UnitType tt.
Global Instance Inhabited_Bool : Inhabited Bool :=
  MkInhabited Bool false.

Global Instance Inhabited_unit : Inhabited unit :=
  MkInhabited unit tt.
Global Instance Inhabited_bool : Inhabited bool :=
  MkInhabited bool false.

(* SAW uses an alternate form of eq_rect where the motive function P also
depends on the equality proof itself *)
Definition Eq__rec (A : Type) (x : A) (P: forall y, x=y -> Type) (p:P x eq_refl) y (e:x=y) :
  P y e.
  dependent inversion e; assumption.
Defined.

Theorem boolEq__eq (b1 b2:bool) : (boolEq b1 b2) = (ite bool b1 b2 (negb b2)).
Proof.
  destruct b1, b2; reflexivity.
Qed.

Definition coerce (a b : sort 0) (p : @eq (sort 0) a b) (x : a) : b :=
  match p in eq _ a' return a' with
  | @eq_refl _ _ => x
  end
.
Check eq_sym.

Definition rcoerce (a b : sort 0) (p : @eq (sort 0) b a) (x : a) : b :=
  coerce a b (eq_sym p) x
.

(* SAW's prelude defines iteDep as a bool eliminator whose arguments are
reordered to look more like if-then-else. *)
Definition iteDep (P : bool -> Type) (b : bool) : P true -> P false -> P b :=
  fun Ptrue Pfalse => bool_rect P Ptrue Pfalse b.

Definition ite_eq_iteDep : forall (a : Type) (b : bool) (x y : a),
    @eq a (ite a b x y) (iteDep (fun _ => a) b x y).
Proof.
  reflexivity.
Defined.

Definition iteDep_True : forall (p : bool -> Type), forall (f1 : p true), forall (f2 : p false), (@eq (p true) (iteDep p true f1 f2)) f1.
Proof.
  reflexivity.
Defined.

Definition iteDep_False : forall (p : bool -> Type), forall (f1 : p true), forall (f2 : p false), (@eq (p false) (iteDep p false f1 f2)) f2.
Proof.
  reflexivity.
Defined.

Definition not__eq (b : bool) : @eq bool (negb b) (ite bool b false true).
Proof.
  reflexivity.
Defined.

Definition and__eq (b1 b2 : bool) : @eq bool (andb b1 b2) (ite bool b1 b2 false).
Proof.
  reflexivity.
Defined.

Definition or__eq (b1 b2 : bool) : @eq bool (orb b1 b2) (ite bool b1 true b2).
Proof.
  reflexivity.
Defined.

Definition xor__eq (b1 b2 : bool) : @eq bool (xorb b1 b2) (ite bool b1 (negb b2) b2).
Proof.
  destruct b1; destruct b2; reflexivity.
Defined.

(*
Definition eq__eq (b1 b2 : bool) : @eq bool (eq b1 b2) (ite bool b1 b2 (negb b2)).
Proof.
  destruct b1; destruct b2; reflexivity.
Defined.
*)

Theorem ite_bit (b c d : bool) : @eq bool (ite bool b c d) (andb (orb (negb b) c) (orb b d)).
Proof.
  destruct b, c, d; reflexivity.
Qed.

(* TODO: doesn't actually coerce *)
Definition sawCoerce {T : Type} (a b : Type) (_ : T) (x : a) := x.

(* TODO: doesn't actually coerce *)
Definition sawUnsafeCoerce (a b : Type) (x : a) := x.

(** DEPRECATED: Use [nat] instead. *)
Definition Nat := nat.

(** DEPRECATED: Use [nat_rect] instead. *)
Definition Nat_rect := nat_rect.

Global Instance Inhabited_Nat : Inhabited Nat :=
  MkInhabited Nat 0%nat.
Global Instance Inhabited_nat : Inhabited nat :=
  MkInhabited nat 0%nat.

Global Hint Resolve (0%nat : nat) : inh.
Global Hint Resolve (0%nat : Nat) : inh.

Definition IsLeNat := @le.
Definition IsLeNat_base (n:nat) : IsLeNat n n := le_n n.
Definition IsLeNat_succ (n m:nat) : IsLeNat n m -> IsLeNat n (S m) := le_S n m.

Definition IsLeNat__rec
  (n : nat)
  (p : forall (x : nat), IsLeNat n x -> Prop)
  (Hbase : p n (IsLeNat_base n))
  (Hstep : forall (x : nat) (H : IsLeNat n x), p x H -> p (S x) (IsLeNat_succ n x H))
  : forall (m : nat) (Hm : IsLeNat n m), p m Hm :=
  fix rec (m:nat) (Hm : IsLeNat n m) {struct Hm} : p m Hm :=
            match Hm as Hm' in le _ m' return p m' Hm' with
            | @le_n _ => Hbase
            | @le_S _ m H => Hstep m H (rec m H)
            end.

(* We could have SAW autogenerate this definition in SAWCorePrelude, but it is
   convenient to place it here so that it can be used in
   SAWCoreVectorsAsCoqVectors.v, which cannot import SAWCorePrelude. *)
Definition IsLtNat := @lt.

(* Definition minNat := Nat.min. *)

Definition uncurry (a b c : Type) (f : a -> b -> c) (p : a * (b * unit)) : c  :=
  f (fst p) (fst (snd p)).

Definition widthNat (n : nat) : nat := 1 + Nat.log2 n.

Definition divModNat (x y : nat) : (nat * nat) :=
  match y with
  | 0 => (y, y)
  | S y'=>
    let (p, q) := Nat.divmod x y' 0 y' in
    (p, y' - q)
  end.

Definition PairType := prod.
Definition PairValue := @pair.
Definition Pair__rec := prod_rect.

(* NOTE: SAW core pair projections do not take type arguments, so these must be
implicit arguments in the translation *)
Arguments Datatypes.fst {_ _}.
Arguments Datatypes.snd {_ _}.

Definition Zero := O.
Definition Succ := S.

Definition addNat := Nat.add.
Definition mulNat := Nat.mul.
Definition equalNat := Nat.eqb.
Definition ltNat := Nat.ltb.
Definition leNat := Nat.leb.
Definition minNat := Nat.min.
Definition maxNat := Nat.max.
Definition Nat__rec := nat_rect.

Fixpoint expNat b n : nat :=
  match n with
  | 0 => S 0
  | S n' => Nat.mul b (expNat b n')
  end.

(* Designed so that 'subNat i 0' reduces to 'i'. *)
Fixpoint subNat m n {struct n} : nat :=
  match n with
  | 0 => m
  | S n' =>
      match m with
      | 0 => 0
      | S m' => subNat m' n'
      end
  end.

Definition if0Nat (a : Type) (n : Nat) (x y : a) : a :=
  match n with
  | 0 => x
  | S _ => y
  end.

Definition Pos_cases
  (a : Type)
  (one : a)
  (b0 : positive -> a -> a)
  (b1 : positive -> a -> a)
  : positive -> a :=
  positive_rect _ b1 b0 one.


Global Instance Inhabited_Pair (a b:Type) {Ha : Inhabited a} {Hb : Inhabited b} : Inhabited (PairType a b) :=
    MkInhabited (PairType a b) (PairValue a b inhabitant inhabitant).
Global Instance Inhabited_prod (a b:Type) {Ha : Inhabited a} {Hb : Inhabited b} : Inhabited (prod a b) :=
    MkInhabited (prod a b) (pair inhabitant inhabitant).


(***
 *** Integers
 ***)

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
Definition intEq : Integer -> Integer -> bool := Z.eqb.
Definition intLe : Integer -> Integer -> bool := Z.leb.
Definition intLt : Integer -> Integer -> bool := Z.ltb.
Definition intToNat : Integer -> nat := Z.to_nat.
Definition natToInt : nat -> Integer := Z.of_nat.

Global Instance Inhabited_Intger : Inhabited Integer :=
  MkInhabited Integer 0%Z.
Global Instance Inhabited_Z : Inhabited Z :=
  MkInhabited Z 0%Z.

Global Hint Resolve (0%Z : Z) : inh.
Global Hint Resolve (0%Z : Integer) : inh.


(***
 *** IntMod
 ***)

(* NOTE: the following will be nonsense for values of n <= 1 *)
Definition IntMod (n : nat) := Z.
Definition toIntMod (n : nat) : Integer -> IntMod n := fun i => Z.modulo i (Z.of_nat n).
Definition fromIntMod (n : nat) : (IntMod n) -> Integer := ZModulo.to_Z (Pos.of_nat n).
Local Notation "[| a |]_ n" := (to_Z (Pos.of_nat n) a) (at level 0, a at level 99).
Definition intModEq (n : nat) (a : IntMod n) (b : IntMod n) : bool
  := Z.eqb [| a |]_n [| b |]_n.
Definition intModAdd : forall (n : nat), (IntMod n) -> (IntMod n) -> IntMod n
  := fun _ => ZModulo.add.
Definition intModSub : forall (n : nat), (IntMod n) -> (IntMod n) -> IntMod n
  := fun _ => ZModulo.sub.
Definition intModMul : forall (n : nat), (IntMod n) -> (IntMod n) -> IntMod n
  := fun _ => ZModulo.mul.
Definition intModNeg : forall (n : nat), (IntMod n) -> IntMod n
  := fun _ => ZModulo.opp.

Global Instance Inhabited_IntMod (n:nat) : Inhabited (IntMod n) :=
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
Variant RecordTypeCons (str:string) (tp:Type) (rest_tp:Type) : Type :=
  RecordCons (x:tp) (rest:rest_tp) : RecordTypeCons str tp rest_tp.

Arguments RecordTypeCons str%string_scope tp rest_tp.
Arguments RecordCons str%string_scope {tp rest_tp} x rest.

Global Instance Inhabited_RecordNil : Inhabited RecordTypeNil :=
    MkInhabited RecordTypeNil RecordNil.
Global Instance Inhabited_RecordCons (fnm:string) (tp rest_tp:Type)
  {Htp : Inhabited tp} {Hrest : Inhabited rest_tp}
  : Inhabited (RecordTypeCons fnm tp rest_tp)
  := MkInhabited (RecordTypeCons fnm tp rest_tp) (RecordCons fnm inhabitant inhabitant).

(* Get the head element of a non-empty record type *)
(* NOTE: more recent versions of Coq seem to have changed constructor patterns
so that the parameters of an inductive type are not required, even when they are
specified in the Arguments declaration, so we use the explicit arguments
@RecordCons pattern, since that does not change between Coq versions *)
Definition recordHead {str tp rest_tp} (r:RecordTypeCons str tp rest_tp) : tp :=
  match r with
  | @RecordCons _ _ _ x _ => x
  end.

(* Get the tail of a non-empty record type *)
Definition recordTail {str tp rest_tp} (r:RecordTypeCons str tp rest_tp) : rest_tp :=
  match r with
  | @RecordCons _ _ _ _ rest => rest
  end.

(* An inductive description of a string being a field in a record type *)
Inductive IsRecordField (str:string) : Type -> Type :=
| IsRecordField_Base tp rtp : IsRecordField str (RecordTypeCons str tp rtp)
| IsRecordField_Step str' tp rtp : IsRecordField str rtp ->
                                   IsRecordField str (RecordTypeCons str' tp rtp).

(* We want to use this as a typeclass, with its constructors for instances *)
Existing Class IsRecordField.
Global Hint Constructors IsRecordField : typeclass_instances.

(* If str is a field in record type rtp, get its associated type *)
Fixpoint getRecordFieldType rtp str `{irf:IsRecordField str rtp} : Type :=
  match irf with
  | @IsRecordField_Base _ tp rtp => tp
  | @IsRecordField_Step _ _ _ _ irf' => @getRecordFieldType _ _ irf'
  end.

(* If str is a field in record r of record type rtp, get its associated value *)
Fixpoint getRecordField {rtp} str `{irf:IsRecordField str rtp} :
  rtp -> getRecordFieldType rtp str :=
  match irf in IsRecordField _ rtp
        return rtp -> getRecordFieldType rtp str (irf:=irf) with
  | @IsRecordField_Base _ tp rtp' => fun r => recordHead r
  | @IsRecordField_Step _ _ _ _ irf' =>
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
