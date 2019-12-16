From Coq          Require Import Lists.List.
Import            ListNotations.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From Records      Require Import Records.



Module SAWCorePrelude.

(* Prelude.id was skipped *)

(* Prelude.fix was skipped *)

(* Prelude.UnitType was skipped *)

(* Prelude.UnitType__rec was skipped *)

(* Prelude.PairType was skipped *)

Definition pair_example : forall (a : Type), forall (b : Type), (a) -> (b) -> ((@PairType) (a) (b)) :=
  (fun (a : Type) (b : Type) (x : a) (y : b) => ((@PairValue) (a) (b) (x) (y))).

(* Prelude.Pair__rec was skipped *)

Definition Pair_fst : forall (a : Type), forall (b : Type), (((@PairType) (a) (b))) -> a :=
  (fun (a : Type) (b : Type) => ((@SAWCoreScaffolding.Pair__rec) (a) (b) ((fun (p : ((@PairType) (a) (b))) => a)) ((fun (x : a) (y : b) => x)))).

Definition Pair_snd : forall (a : Type), forall (b : Type), (((@PairType) (a) (b))) -> b :=
  (fun (a : Type) (b : Type) => ((@SAWCoreScaffolding.Pair__rec) (a) (b) ((fun (p : ((@PairType) (a) (b))) => b)) ((fun (x : a) (y : b) => y)))).

(* Prelude.fst was skipped *)

(* Prelude.snd was skipped *)

Definition uncurry : forall (a : Type), forall (b : Type), forall (c : Type), forall (f : (a) -> (b) -> c), (((prod) (a) (b))) -> c :=
  (fun (a : Type) (b : Type) (c : Type) (f : (a) -> (b) -> c) (x : ((prod) (a) (b))) => ((f) (((fst) (x))) (((snd) (x))))).

(* Prelude.String was skipped *)

(* Prelude.error was skipped *)

(* Prelude.EmptyType was skipped *)

(* Prelude.EmptyType__rec was skipped *)

(* Prelude.RecordType was skipped *)

(* Prelude.RecordType__rec was skipped *)

(* Prelude.Eq was skipped *)

(* Prelude.Eq__rec was skipped *)

Definition eq_cong : forall (t : Type), forall (x : t), forall (y : t), (((@Eq) (t) (x) (y))) -> forall (u : Type), forall (f : (t) -> u), ((@Eq) (u) (((f) (x))) (((f) (y)))) :=
  (fun (t : Type) (x : t) (y : t) (eq : ((@Eq) (t) (x) (y))) (u : Type) (f : (t) -> u) => ((@SAWCoreScaffolding.Eq__rec) (t) (x) ((fun (y' : t) (eq' : ((@Eq) (t) (x) (y'))) => ((@Eq) (u) (((f) (x))) (((f) (y')))))) (((@Refl) (u) (((f) (x))))) (y) (eq))).

Definition sym : forall (a : Type), forall (x : a), forall (y : a), (((@Eq) (a) (x) (y))) -> ((@Eq) (a) (y) (x)) :=
  (fun (a : Type) (x : a) (y : a) (eq : ((@Eq) (a) (x) (y))) => ((@SAWCoreScaffolding.Eq__rec) (a) (x) ((fun (y' : a) (eq' : ((@Eq) (a) (x) (y'))) => ((@Eq) (a) (y') (x)))) (((@Refl) (a) (x))) (y) (eq))).

Definition trans : forall (a : Type), forall (x : a), forall (y : a), forall (z : a), (((@Eq) (a) (x) (y))) -> (((@Eq) (a) (y) (z))) -> ((@Eq) (a) (x) (z)) :=
  (fun (a : Type) (x : a) (y : a) (z : a) (eq1 : ((@Eq) (a) (x) (y))) (eq2 : ((@Eq) (a) (y) (z))) => ((@SAWCoreScaffolding.Eq__rec) (a) (y) ((fun (y' : a) (eq' : ((@Eq) (a) (y) (y'))) => ((@Eq) (a) (x) (y')))) (eq1) (z) (eq2))).

Definition trans2 : forall (a : Type), forall (x : a), forall (y : a), forall (z : a), (((@Eq) (a) (x) (z))) -> (((@Eq) (a) (y) (z))) -> ((@Eq) (a) (x) (y)) :=
  (fun (a : Type) (x : a) (y : a) (z : a) (eq1 : ((@Eq) (a) (x) (z))) (eq2 : ((@Eq) (a) (y) (z))) => ((@SAWCorePrelude.trans) (a) (x) (z) (y) (eq1) (((@SAWCorePrelude.sym) (a) (y) (z) (eq2))))).

Definition trans4 : forall (a : Type), forall (w : a), forall (x : a), forall (y : a), forall (z : a), (((@Eq) (a) (w) (x))) -> (((@Eq) (a) (x) (y))) -> (((@Eq) (a) (y) (z))) -> ((@Eq) (a) (w) (z)) :=
  (fun (a : Type) (w : a) (x : a) (y : a) (z : a) (eq1 : ((@Eq) (a) (w) (x))) (eq2 : ((@Eq) (a) (x) (y))) (eq3 : ((@Eq) (a) (y) (z))) => ((@SAWCorePrelude.trans) (a) (w) (x) (z) (eq1) (((@SAWCorePrelude.trans) (a) (x) (y) (z) (eq2) (eq3))))).

Definition eq_inv_map : forall (a : Type), forall (b : Type), forall (a1 : a), forall (a2 : a), (((@Eq) (a) (a1) (a2))) -> forall (f1 : (a) -> b), forall (f2 : (a) -> b), (((@Eq) (b) (((f1) (a2))) (((f2) (a2))))) -> ((@Eq) (b) (((f1) (a1))) (((f2) (a1)))) :=
  (fun (a : Type) (b : Type) (a1 : a) (a2 : a) (eq_a : ((@Eq) (a) (a1) (a2))) (f1 : (a) -> b) (f2 : (a) -> b) (eq_f : ((@Eq) (b) (((f1) (a2))) (((f2) (a2))))) => ((@SAWCorePrelude.trans) (b) (((f1) (a1))) (((f1) (a2))) (((f2) (a1))) (((@SAWCorePrelude.eq_cong) (a) (a1) (a2) (eq_a) (b) (f1))) (((@SAWCorePrelude.trans) (b) (((f1) (a2))) (((f2) (a2))) (((f2) (a1))) (eq_f) (((@SAWCorePrelude.eq_cong) (a) (a2) (a1) (((@SAWCorePrelude.sym) (a) (a1) (a2) (eq_a))) (b) (f2))))))).

(* Prelude.unsafeAssert was skipped *)

(* Prelude.coerce was skipped *)

(* Prelude.coerce__def was skipped *)

(* Prelude.coerce__eq was skipped *)

(* Prelude.rcoerce was skipped *)

(* Prelude.unsafeCoerce was skipped *)

(* Prelude.unsafeCoerce_same was skipped *)

Definition piCong0 : forall (r : Type), forall (x : Type), forall (y : Type), (((@Eq) (Type) (x) (y))) -> ((@Eq) (Type) ((x) -> r) ((y) -> r)) :=
  (fun (r : Type) (x : Type) (y : Type) (eq : ((@Eq) (Type) (x) (y))) => ((@SAWCoreScaffolding.Eq__rec) (Type) (x) ((fun (y' : Type) (eq' : ((@Eq) (Type) (x) (y'))) => ((@Eq) (Type) ((x) -> r) ((y') -> r)))) (((@Refl) (Type) ((x) -> r))) (y) (eq))).

Definition piCong1 : forall (r : Type), forall (x : Type), forall (y : Type), (((@Eq) (Type) (x) (y))) -> ((@Eq) (Type) ((r) -> x) ((r) -> y)) :=
  (fun (r : Type) (x : Type) (y : Type) (eq : ((@Eq) (Type) (x) (y))) => ((@SAWCoreScaffolding.Eq__rec) (Type) (x) ((fun (y' : Type) (eq' : ((@Eq) (Type) (x) (y'))) => ((@Eq) (Type) ((r) -> x) ((r) -> y')))) (((@Refl) (Type) ((r) -> x))) (y) (eq))).

Inductive Bit : Type :=
| Bit1 : ((@Bit))
| Bit0 : ((@Bit))
.

Definition Bit__rec : forall (p : (((@Bit))) -> Type), (((p) (((@Bit1))))) -> (((p) (((@Bit0))))) -> forall (b : ((@Bit))), ((p) (b)) :=
  (fun (p : (((@Bit))) -> Type) (f1 : ((p) (((@Bit1))))) (f2 : ((p) (((@Bit0))))) (b : ((@Bit))) => ((@Bit_rect) (p) (f1) (f2) (b))).

(* Prelude.Bool was skipped *)

(* Prelude.True was skipped *)

(* Prelude.False was skipped *)

(* Prelude.iteDep was skipped *)

(* Prelude.iteDep_True was skipped *)

(* Prelude.iteDep_False was skipped *)

(* Prelude.ite was skipped *)

(* Prelude.ite_eq_iteDep was skipped *)

Definition ite_true : forall (a : Type), forall (x : a), forall (y : a), ((@Eq) (a) (if @SAWCoreScaffolding.True then x else y) (x)) :=
  (fun (a : Type) (x : a) (y : a) => ((@SAWCorePrelude.trans) (a) (if @SAWCoreScaffolding.True then x else y) (((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => a)) (@SAWCoreScaffolding.True) (x) (y))) (x) (((@SAWCoreScaffolding.ite_eq_iteDep) (a) (@SAWCoreScaffolding.True) (x) (y))) (((@SAWCoreScaffolding.iteDep_True) ((fun (_ : @SAWCoreScaffolding.Bool) => a)) (x) (y))))).

Definition ite_false : forall (a : Type), forall (x : a), forall (y : a), ((@Eq) (a) (if @SAWCoreScaffolding.False then x else y) (y)) :=
  (fun (a : Type) (x : a) (y : a) => ((@SAWCorePrelude.trans) (a) (if @SAWCoreScaffolding.False then x else y) (((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => a)) (@SAWCoreScaffolding.False) (x) (y))) (y) (((@SAWCoreScaffolding.ite_eq_iteDep) (a) (@SAWCoreScaffolding.False) (x) (y))) (((@SAWCoreScaffolding.iteDep_False) ((fun (_ : @SAWCoreScaffolding.Bool) => a)) (x) (y))))).

Definition bool2bit : (@SAWCoreScaffolding.Bool) -> ((@Bit)) :=
  (fun (b : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (_ : @SAWCoreScaffolding.Bool) => ((@Bit)))) (b) (((@Bit1))) (((@Bit0))))).

Definition bool2bit_True : ((@Eq) (((@Bit))) (((@SAWCorePrelude.bool2bit) (@SAWCoreScaffolding.True))) (((@Bit1)))) :=
  ((@SAWCoreScaffolding.iteDep_True) ((fun (_ : @SAWCoreScaffolding.Bool) => ((@Bit)))) (((@Bit1))) (((@Bit0)))).

Definition bool2bit_False : ((@Eq) (((@Bit))) (((@SAWCorePrelude.bool2bit) (@SAWCoreScaffolding.False))) (((@Bit0)))) :=
  ((@SAWCoreScaffolding.iteDep_False) ((fun (_ : @SAWCoreScaffolding.Bool) => ((@Bit)))) (((@Bit1))) (((@Bit0)))).

Definition bit2bool : (((@Bit))) -> @SAWCoreScaffolding.Bool :=
  ((@SAWCorePrelude.Bit__rec) ((fun (_ : ((@Bit))) => @SAWCoreScaffolding.Bool)) (@SAWCoreScaffolding.True) (@SAWCoreScaffolding.False)).

Definition bit2bool_Bit1 : ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCorePrelude.bit2bool) (((@Bit1))))) (@SAWCoreScaffolding.True)) :=
  ((@Refl) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.True)).

Definition bit2bool_Bit0 : ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCorePrelude.bit2bool) (((@Bit0))))) (@SAWCoreScaffolding.False)) :=
  ((@Refl) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.False)).

(* Prelude.not was skipped *)

(* Prelude.not__eq was skipped *)

(* Prelude.and was skipped *)

(* Prelude.and__eq was skipped *)

(* Prelude.or was skipped *)

(* Prelude.or__eq was skipped *)

(* Prelude.xor was skipped *)

(* Prelude.xor__eq was skipped *)

(* Prelude.boolEq was skipped *)

(* Prelude.boolEq__eq was skipped *)

Definition implies : (@SAWCoreScaffolding.Bool) -> (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool :=
  (fun (a : @SAWCoreScaffolding.Bool) (b : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (a))) (b))).

Definition implies__eq : forall (a : @SAWCoreScaffolding.Bool), forall (b : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCorePrelude.implies) (a) (b))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (a))) (b)))) :=
  (fun (a : @SAWCoreScaffolding.Bool) (b : @SAWCoreScaffolding.Bool) => ((@Refl) (@SAWCoreScaffolding.Bool) (((@SAWCorePrelude.implies) (a) (b))))).

Definition not_True : ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False)) :=
  ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (if @SAWCoreScaffolding.True then @SAWCoreScaffolding.False else @SAWCoreScaffolding.True) (@SAWCoreScaffolding.False) (((@SAWCoreScaffolding.not__eq) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.ite_true) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.False) (@SAWCoreScaffolding.True)))).

Definition not_False : ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True)) :=
  ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (if @SAWCoreScaffolding.False then @SAWCoreScaffolding.False else @SAWCoreScaffolding.True) (@SAWCoreScaffolding.True) (((@SAWCoreScaffolding.not__eq) (@SAWCoreScaffolding.False))) (((@SAWCorePrelude.ite_false) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.False) (@SAWCoreScaffolding.True)))).

Definition not_not : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.not) (x))))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.not) (b))))) (b)))) (x) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (@SAWCorePrelude.not_True) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.not))) (@SAWCorePrelude.not_False))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (@SAWCorePrelude.not_False) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.not))) (@SAWCorePrelude.not_True))))).

Definition and_True1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.True) (x))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.True) (x))) (if @SAWCoreScaffolding.True then x else @SAWCoreScaffolding.False) (x) (((@SAWCoreScaffolding.and__eq) (@SAWCoreScaffolding.True) (x))) (((@SAWCorePrelude.ite_true) (@SAWCoreScaffolding.Bool) (x) (@SAWCoreScaffolding.False))))).

Definition and_False1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.False) (x))) (@SAWCoreScaffolding.False)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.False) (x))) (if @SAWCoreScaffolding.False then x else @SAWCoreScaffolding.False) (@SAWCoreScaffolding.False) (((@SAWCoreScaffolding.and__eq) (@SAWCoreScaffolding.False) (x))) (((@SAWCorePrelude.ite_false) (@SAWCoreScaffolding.Bool) (x) (@SAWCoreScaffolding.False))))).

Definition and_True2 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x) (@SAWCoreScaffolding.True))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (b) (@SAWCoreScaffolding.True))) (b)))) (x) (((@SAWCorePrelude.and_True1) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.and_False1) (@SAWCoreScaffolding.True))))).

Definition and_False2 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.False)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (b) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.False)))) (x) (((@SAWCorePrelude.and_True1) (@SAWCoreScaffolding.False))) (((@SAWCorePrelude.and_False1) (@SAWCoreScaffolding.False))))).

Definition and_assoc : forall (x : @SAWCoreScaffolding.Bool), forall (y : @SAWCoreScaffolding.Bool), forall (z : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.and) (y) (z))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.and) (x) (y))) (z)))) :=
  (fun (x : @SAWCoreScaffolding.Bool) (y : @SAWCoreScaffolding.Bool) (z : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.and) (y) (b))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.and) (x) (y))) (b)))))) (z) (((@SAWCorePrelude.trans2) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.and) (y) (@SAWCoreScaffolding.True))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.and) (x) (y))) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.and) (x) (y))) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (y) (@SAWCoreScaffolding.True))) (y) (((@SAWCorePrelude.and_True2) (y))) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x))))) (((@SAWCorePrelude.and_True2) (((@SAWCoreScaffolding.and) (x) (y))))))) (((@SAWCorePrelude.trans2) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.and) (y) (@SAWCoreScaffolding.False))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.and) (x) (y))) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.and) (y) (@SAWCoreScaffolding.False))))) (((@SAWCoreScaffolding.and) (x) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (y) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.and_False2) (y))) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x))))) (((@SAWCorePrelude.and_False2) (x))))) (((@SAWCorePrelude.and_False2) (((@SAWCoreScaffolding.and) (x) (y))))))))).

Definition and_idem : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x) (x))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (b) (b))) (b)))) (x) (((@SAWCorePrelude.and_True1) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.and_False1) (@SAWCoreScaffolding.False))))).

Definition or_True1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.True) (x))) (@SAWCoreScaffolding.True)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.True) (x))) (if @SAWCoreScaffolding.True then @SAWCoreScaffolding.True else x) (@SAWCoreScaffolding.True) (((@SAWCoreScaffolding.or__eq) (@SAWCoreScaffolding.True) (x))) (((@SAWCorePrelude.ite_true) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.True) (x))))).

Definition or_False1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.False) (x))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.False) (x))) (if @SAWCoreScaffolding.False then @SAWCoreScaffolding.True else x) (x) (((@SAWCoreScaffolding.or__eq) (@SAWCoreScaffolding.False) (x))) (((@SAWCorePrelude.ite_false) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.True) (x))))).

Definition or_True2 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (x) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.True)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (b) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.True)))) (x) (((@SAWCorePrelude.or_True1) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.or_False1) (@SAWCoreScaffolding.True))))).

Definition or_False2 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (x) (@SAWCoreScaffolding.False))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (b) (@SAWCoreScaffolding.False))) (b)))) (x) (((@SAWCorePrelude.or_True1) (@SAWCoreScaffolding.False))) (((@SAWCorePrelude.or_False1) (@SAWCoreScaffolding.False))))).

Definition or_assoc : forall (x : @SAWCoreScaffolding.Bool), forall (y : @SAWCoreScaffolding.Bool), forall (z : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.or) (y) (z))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.or) (x) (y))) (z)))) :=
  (fun (x : @SAWCoreScaffolding.Bool) (y : @SAWCoreScaffolding.Bool) (z : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.or) (y) (b))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.or) (x) (y))) (b)))))) (z) (((@SAWCorePrelude.trans2) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.or) (y) (@SAWCoreScaffolding.True))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.or) (x) (y))) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.or) (y) (@SAWCoreScaffolding.True))))) (((@SAWCoreScaffolding.or) (x) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (y) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.or_True2) (y))) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (x))))) (((@SAWCorePrelude.or_True2) (x))))) (((@SAWCorePrelude.or_True2) (((@SAWCoreScaffolding.or) (x) (y))))))) (((@SAWCorePrelude.trans2) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.or) (y) (@SAWCoreScaffolding.False))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.or) (x) (y))) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.or) (x) (y))) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (y) (@SAWCoreScaffolding.False))) (y) (((@SAWCorePrelude.or_False2) (y))) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (x))))) (((@SAWCorePrelude.or_False2) (((@SAWCoreScaffolding.or) (x) (y))))))))).

Definition or_idem : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (x) (x))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (b) (b))) (b)))) (x) (((@SAWCorePrelude.or_True1) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.or_False1) (@SAWCoreScaffolding.False))))).

Definition implies_True1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCorePrelude.implies) (@SAWCoreScaffolding.True) (x))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (x))) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.False) (x))) (x) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (@SAWCorePrelude.not_True) (@SAWCoreScaffolding.Bool) ((fun (y : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.or) (y) (x)))))) (((@SAWCorePrelude.or_False1) (x))))).

Definition implies_False1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCorePrelude.implies) (@SAWCoreScaffolding.False) (x))) (@SAWCoreScaffolding.True)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (x))) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.True) (x))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (@SAWCorePrelude.not_False) (@SAWCoreScaffolding.Bool) ((fun (y : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.or) (y) (x)))))) (((@SAWCorePrelude.or_True1) (x))))).

Definition true_implies : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCorePrelude.implies) (@SAWCoreScaffolding.True) (x))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCorePrelude.implies_True1) (x))).

Definition xor_True1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (@SAWCoreScaffolding.True) (x))) (((@SAWCoreScaffolding.not) (x)))) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (@SAWCoreScaffolding.True) (x))) (if @SAWCoreScaffolding.True then ((@SAWCoreScaffolding.not) (x)) else x) (((@SAWCoreScaffolding.not) (x))) (((@SAWCoreScaffolding.xor__eq) (@SAWCoreScaffolding.True) (x))) (((@SAWCorePrelude.ite_true) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (x))) (x))))).

Definition xor_False1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (@SAWCoreScaffolding.False) (x))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (@SAWCoreScaffolding.False) (x))) (if @SAWCoreScaffolding.False then ((@SAWCoreScaffolding.not) (x)) else x) (x) (((@SAWCoreScaffolding.xor__eq) (@SAWCoreScaffolding.False) (x))) (((@SAWCorePrelude.ite_false) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (x))) (x))))).

Definition xor_False2 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (x) (@SAWCoreScaffolding.False))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (b) (@SAWCoreScaffolding.False))) (b)))) (x) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (@SAWCoreScaffolding.True) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.xor_True1) (@SAWCoreScaffolding.False))) (@SAWCorePrelude.not_False))) (((@SAWCorePrelude.xor_False1) (@SAWCoreScaffolding.False))))).

Definition xor_True2 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (x) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.not) (x)))) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (b) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.not) (b)))))) (x) (((@SAWCorePrelude.xor_True1) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.trans2) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (@SAWCoreScaffolding.False) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.xor_False1) (@SAWCoreScaffolding.True))) (@SAWCorePrelude.not_False))))).

Definition xor_same : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (x) (x))) (@SAWCoreScaffolding.False)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (b) (b))) (@SAWCoreScaffolding.False)))) (x) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.xor) (@SAWCoreScaffolding.True) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.xor_True1) (@SAWCoreScaffolding.True))) (@SAWCorePrelude.not_True))) (((@SAWCorePrelude.xor_False1) (@SAWCoreScaffolding.False))))).

Definition boolEq_True1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (@SAWCoreScaffolding.True) (x))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (@SAWCoreScaffolding.True) (x))) (if @SAWCoreScaffolding.True then x else ((@SAWCoreScaffolding.not) (x))) (x) (((@SAWCoreScaffolding.boolEq__eq) (@SAWCoreScaffolding.True) (x))) (((@SAWCorePrelude.ite_true) (@SAWCoreScaffolding.Bool) (x) (((@SAWCoreScaffolding.not) (x))))))).

Definition boolEq_False1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (@SAWCoreScaffolding.False) (x))) (((@SAWCoreScaffolding.not) (x)))) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (@SAWCoreScaffolding.False) (x))) (if @SAWCoreScaffolding.False then x else ((@SAWCoreScaffolding.not) (x))) (((@SAWCoreScaffolding.not) (x))) (((@SAWCoreScaffolding.boolEq__eq) (@SAWCoreScaffolding.False) (x))) (((@SAWCorePrelude.ite_false) (@SAWCoreScaffolding.Bool) (x) (((@SAWCoreScaffolding.not) (x))))))).

Definition boolEq_True2 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (x) (@SAWCoreScaffolding.True))) (x)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (b) (@SAWCoreScaffolding.True))) (b)))) (x) (((@SAWCorePrelude.boolEq_True1) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (@SAWCoreScaffolding.False) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.boolEq_False1) (@SAWCoreScaffolding.True))) (@SAWCorePrelude.not_True))))).

Definition boolEq_False2 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (x) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.not) (x)))) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (b) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.not) (b)))))) (x) (((@SAWCorePrelude.trans2) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (@SAWCoreScaffolding.True) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.boolEq_True1) (@SAWCoreScaffolding.False))) (@SAWCorePrelude.not_True))) (((@SAWCorePrelude.boolEq_False1) (@SAWCoreScaffolding.False))))).

Definition boolEq_same : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (x) (x))) (@SAWCoreScaffolding.True)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (b) (b))) (@SAWCoreScaffolding.True)))) (x) (((@SAWCorePrelude.boolEq_True1) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.boolEq) (@SAWCoreScaffolding.False) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.boolEq_False1) (@SAWCoreScaffolding.False))) (@SAWCorePrelude.not_False))))).

Definition not_or : forall (x : @SAWCoreScaffolding.Bool), forall (y : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.or) (x) (y))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (x))) (((@SAWCoreScaffolding.not) (y)))))) :=
  (fun (x : @SAWCoreScaffolding.Bool) (y : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.or) (b) (y))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (b))) (((@SAWCoreScaffolding.not) (y)))))))) (x) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.True) (y))))) (@SAWCoreScaffolding.False) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.True) (y))))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.True) (y))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.or_True1) (y))) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.not))) (@SAWCorePrelude.not_True))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.False) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.False) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.False) (((@SAWCoreScaffolding.not) (y))))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.and_False1) (((@SAWCoreScaffolding.not) (y))))))) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.False) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (@SAWCorePrelude.not_True))) (@SAWCoreScaffolding.Bool) ((fun (z : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.and) (z) (((@SAWCoreScaffolding.not) (y)))))))))))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.False) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.False) (y))) (y) (((@SAWCorePrelude.or_False1) (y))) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.not))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.True) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (@SAWCorePrelude.not_False) (@SAWCoreScaffolding.Bool) ((fun (z : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.and) (z) (((@SAWCoreScaffolding.not) (y)))))))) (((@SAWCorePrelude.and_True1) (((@SAWCoreScaffolding.not) (y))))))))))))).

Definition not_and : forall (x : @SAWCoreScaffolding.Bool), forall (y : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.and) (x) (y))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (x))) (((@SAWCoreScaffolding.not) (y)))))) :=
  (fun (x : @SAWCoreScaffolding.Bool) (y : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.and) (b) (y))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (b))) (((@SAWCoreScaffolding.not) (y)))))))) (x) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.True) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.True) (y))) (y) (((@SAWCorePrelude.and_True1) (y))) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.not))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.False) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (@SAWCorePrelude.not_True) (@SAWCoreScaffolding.Bool) ((fun (z : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.or) (z) (((@SAWCoreScaffolding.not) (y)))))))) (((@SAWCorePrelude.or_False1) (((@SAWCoreScaffolding.not) (y))))))))))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.False) (y))))) (@SAWCoreScaffolding.True) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.False) (y))))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.False) (y))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.and_False1) (y))) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.not))) (@SAWCorePrelude.not_False))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.True) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.True) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.True) (((@SAWCoreScaffolding.not) (y))))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.or_True1) (((@SAWCoreScaffolding.not) (y))))))) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.True) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (@SAWCorePrelude.not_False))) (@SAWCoreScaffolding.Bool) ((fun (z : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.or) (z) (((@SAWCoreScaffolding.not) (y)))))))))))))).

Definition ite_not : forall (a : Type), forall (b : @SAWCoreScaffolding.Bool), forall (x : a), forall (y : a), ((@Eq) (a) (if ((@SAWCoreScaffolding.not) (b)) then x else y) (if b then y else x)) :=
  (fun (a : Type) (b : @SAWCoreScaffolding.Bool) (x : a) (y : a) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : @SAWCoreScaffolding.Bool) => ((@Eq) (a) (if ((@SAWCoreScaffolding.not) (b')) then x else y) (if b' then y else x)))) (b) (((@SAWCorePrelude.trans) (a) (if ((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True)) then x else y) (y) (if @SAWCoreScaffolding.True then y else x) (((@SAWCorePrelude.trans) (a) (if ((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True)) then x else y) (if @SAWCoreScaffolding.False then x else y) (y) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (@SAWCorePrelude.not_True) (a) ((fun (z : @SAWCoreScaffolding.Bool) => if z then x else y)))) (((@SAWCorePrelude.ite_false) (a) (x) (y))))) (((@SAWCorePrelude.sym) (a) (if @SAWCoreScaffolding.True then y else x) (y) (((@SAWCorePrelude.ite_true) (a) (y) (x))))))) (((@SAWCorePrelude.trans) (a) (if ((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False)) then x else y) (x) (if @SAWCoreScaffolding.False then y else x) (((@SAWCorePrelude.trans) (a) (if ((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False)) then x else y) (if @SAWCoreScaffolding.True then x else y) (x) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (@SAWCorePrelude.not_False) (a) ((fun (z : @SAWCoreScaffolding.Bool) => if z then x else y)))) (((@SAWCorePrelude.ite_true) (a) (x) (y))))) (((@SAWCorePrelude.sym) (a) (if @SAWCoreScaffolding.False then y else x) (x) (((@SAWCorePrelude.ite_false) (a) (y) (x))))))))).

Definition ite_nest1 : forall (a : Type), forall (b : @SAWCoreScaffolding.Bool), forall (x : a), forall (y : a), forall (z : a), ((@Eq) (a) (if b then if b then x else y else z) (if b then x else z)) :=
  (fun (a : Type) (b : @SAWCoreScaffolding.Bool) (x : a) (y : a) (z : a) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : @SAWCoreScaffolding.Bool) => ((@Eq) (a) (if b' then if b' then x else y else z) (if b' then x else z)))) (b) (((@SAWCorePrelude.trans) (a) (if @SAWCoreScaffolding.True then if @SAWCoreScaffolding.True then x else y else z) (x) (if @SAWCoreScaffolding.True then x else z) (((@SAWCorePrelude.trans) (a) (if @SAWCoreScaffolding.True then if @SAWCoreScaffolding.True then x else y else z) (if @SAWCoreScaffolding.True then x else y) (x) (((@SAWCorePrelude.ite_true) (a) (if @SAWCoreScaffolding.True then x else y) (z))) (((@SAWCorePrelude.ite_true) (a) (x) (y))))) (((@SAWCorePrelude.sym) (a) (if @SAWCoreScaffolding.True then x else z) (x) (((@SAWCorePrelude.ite_true) (a) (x) (z))))))) (((@SAWCorePrelude.trans) (a) (if @SAWCoreScaffolding.False then if @SAWCoreScaffolding.False then x else y else z) (z) (if @SAWCoreScaffolding.False then x else z) (((@SAWCorePrelude.ite_false) (a) (if @SAWCoreScaffolding.False then x else y) (z))) (((@SAWCorePrelude.sym) (a) (if @SAWCoreScaffolding.False then x else z) (z) (((@SAWCorePrelude.ite_false) (a) (x) (z))))))))).

Definition ite_nest2 : forall (a : Type), forall (b : @SAWCoreScaffolding.Bool), forall (x : a), forall (y : a), forall (z : a), ((@Eq) (a) (if b then x else if b then y else z) (if b then x else z)) :=
  (fun (a : Type) (b : @SAWCoreScaffolding.Bool) (x : a) (y : a) (z : a) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : @SAWCoreScaffolding.Bool) => ((@Eq) (a) (if b' then x else if b' then y else z) (if b' then x else z)))) (b) (((@SAWCorePrelude.trans) (a) (if @SAWCoreScaffolding.True then x else if @SAWCoreScaffolding.True then y else z) (x) (if @SAWCoreScaffolding.True then x else z) (((@SAWCorePrelude.ite_true) (a) (x) (if @SAWCoreScaffolding.True then y else z))) (((@SAWCorePrelude.sym) (a) (if @SAWCoreScaffolding.True then x else z) (x) (((@SAWCorePrelude.ite_true) (a) (x) (z))))))) (((@SAWCorePrelude.trans) (a) (if @SAWCoreScaffolding.False then x else if @SAWCoreScaffolding.False then y else z) (z) (if @SAWCoreScaffolding.False then x else z) (((@SAWCorePrelude.trans) (a) (if @SAWCoreScaffolding.False then x else if @SAWCoreScaffolding.False then y else z) (if @SAWCoreScaffolding.False then y else z) (z) (((@SAWCorePrelude.ite_false) (a) (x) (if @SAWCoreScaffolding.False then y else z))) (((@SAWCorePrelude.ite_false) (a) (y) (z))))) (((@SAWCorePrelude.sym) (a) (if @SAWCoreScaffolding.False then x else z) (z) (((@SAWCorePrelude.ite_false) (a) (x) (z))))))))).

(* Prelude.ite_bit was skipped *)

Definition ite_bit_false_1 : forall (b : @SAWCoreScaffolding.Bool), forall (c : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (if b then @SAWCoreScaffolding.False else c) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (b))) (c)))) :=
  (fun (b : @SAWCoreScaffolding.Bool) (c : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (if b' then @SAWCoreScaffolding.False else c) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (b'))) (c)))))) (b) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (if @SAWCoreScaffolding.True then @SAWCoreScaffolding.False else c) (@SAWCoreScaffolding.False) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (c))) (((@SAWCorePrelude.ite_true) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.False) (c))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (c))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (c))) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.False) (c))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (@SAWCorePrelude.not_True) (@SAWCoreScaffolding.Bool) ((fun (z : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.and) (z) (c)))))) (((@SAWCorePrelude.and_False1) (c))))))))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (if @SAWCoreScaffolding.False then @SAWCoreScaffolding.False else c) (c) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (c))) (((@SAWCorePrelude.ite_false) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.False) (c))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (c))) (c) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (c))) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.True) (c))) (c) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (@SAWCorePrelude.not_False) (@SAWCoreScaffolding.Bool) ((fun (z : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.and) (z) (c)))))) (((@SAWCorePrelude.and_True1) (c))))))))))).

Definition ite_bit_true_1 : forall (b : @SAWCoreScaffolding.Bool), forall (c : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (if b then @SAWCoreScaffolding.True else c) (((@SAWCoreScaffolding.or) (b) (c)))) :=
  (fun (b : @SAWCoreScaffolding.Bool) (c : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (if b' then @SAWCoreScaffolding.True else c) (((@SAWCoreScaffolding.or) (b') (c)))))) (b) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (if @SAWCoreScaffolding.True then @SAWCoreScaffolding.True else c) (@SAWCoreScaffolding.True) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.True) (c))) (((@SAWCorePrelude.ite_true) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.True) (c))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.True) (c))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.or_True1) (c))))))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (if @SAWCoreScaffolding.False then @SAWCoreScaffolding.True else c) (c) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.False) (c))) (((@SAWCorePrelude.ite_false) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.True) (c))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.False) (c))) (c) (((@SAWCorePrelude.or_False1) (c))))))))).

Definition ite_fold_not : forall (b : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (if b then @SAWCoreScaffolding.False else @SAWCoreScaffolding.True) (((@SAWCoreScaffolding.not) (b)))) :=
  (fun (b : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (if b' then @SAWCoreScaffolding.False else @SAWCoreScaffolding.True) (((@SAWCoreScaffolding.not) (b')))))) (b) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (if @SAWCoreScaffolding.True then @SAWCoreScaffolding.False else @SAWCoreScaffolding.True) (@SAWCoreScaffolding.False) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.ite_true) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.False) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (@SAWCorePrelude.not_True))))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (if @SAWCoreScaffolding.False then @SAWCoreScaffolding.False else @SAWCoreScaffolding.True) (@SAWCoreScaffolding.True) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (((@SAWCorePrelude.ite_false) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.False) (@SAWCoreScaffolding.True))) (((@SAWCorePrelude.sym) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (@SAWCorePrelude.not_False))))))).

Definition ite_eq : forall (a : Type), forall (b : @SAWCoreScaffolding.Bool), forall (x : a), ((@Eq) (a) (if b then x else x) (x)) :=
  (fun (a : Type) (b : @SAWCoreScaffolding.Bool) (x : a) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : @SAWCoreScaffolding.Bool) => ((@Eq) (a) (if b' then x else x) (x)))) (b) (((@SAWCorePrelude.ite_true) (a) (x) (x))) (((@SAWCorePrelude.ite_false) (a) (x) (x))))).

Definition or_triv1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.not) (x))))) (@SAWCoreScaffolding.True)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (b) (((@SAWCoreScaffolding.not) (b))))) (@SAWCoreScaffolding.True)))) (x) (((@SAWCorePrelude.or_True1) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (@SAWCoreScaffolding.False) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.or_False1) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))))) (@SAWCorePrelude.not_False))))).

Definition or_triv2 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (x))) (x))) (@SAWCoreScaffolding.True)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (b))) (b))) (@SAWCoreScaffolding.True)))) (x) (((@SAWCorePrelude.or_True2) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))))) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.False))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.or_False2) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))))) (@SAWCorePrelude.not_False))))).

Definition and_triv1 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.not) (x))))) (@SAWCoreScaffolding.False)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (b) (((@SAWCoreScaffolding.not) (b))))) (@SAWCoreScaffolding.False)))) (x) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (@SAWCoreScaffolding.True) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.and_True1) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))))) (@SAWCorePrelude.not_True))) (((@SAWCorePrelude.and_False1) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))))))).

Definition and_triv2 : forall (x : @SAWCoreScaffolding.Bool), ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (x))) (x))) (@SAWCoreScaffolding.False)) :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (b : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (b))) (b))) (@SAWCoreScaffolding.False)))) (x) (((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.True))) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))) (@SAWCoreScaffolding.False) (((@SAWCorePrelude.and_True2) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.True))))) (@SAWCorePrelude.not_True))) (((@SAWCorePrelude.and_False2) (((@SAWCoreScaffolding.not) (@SAWCoreScaffolding.False))))))).

Definition EqTrue : (@SAWCoreScaffolding.Bool) -> Type :=
  (fun (x : @SAWCoreScaffolding.Bool) => ((@Eq) (@SAWCoreScaffolding.Bool) (x) (@SAWCoreScaffolding.True))).

Definition TrueI : ((@SAWCorePrelude.EqTrue) (@SAWCoreScaffolding.True)) :=
  ((@Refl) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.True)).

Definition andI : forall (x : @SAWCoreScaffolding.Bool), forall (y : @SAWCoreScaffolding.Bool), (((@SAWCorePrelude.EqTrue) (x))) -> (((@SAWCorePrelude.EqTrue) (y))) -> ((@SAWCorePrelude.EqTrue) (((@SAWCoreScaffolding.and) (x) (y)))) :=
  (fun (x : @SAWCoreScaffolding.Bool) (y : @SAWCoreScaffolding.Bool) (p : ((@Eq) (@SAWCoreScaffolding.Bool) (x) (@SAWCoreScaffolding.True))) (q : ((@Eq) (@SAWCoreScaffolding.Bool) (y) (@SAWCoreScaffolding.True))) => ((@SAWCorePrelude.trans4) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x) (y))) (((@SAWCoreScaffolding.and) (x) (@SAWCoreScaffolding.True))) (x) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.eq_cong) (@SAWCoreScaffolding.Bool) (y) (@SAWCoreScaffolding.True) (q) (@SAWCoreScaffolding.Bool) (((@SAWCoreScaffolding.and) (x))))) (((@SAWCorePrelude.and_True2) (x))) (p))).

Definition impliesI : forall (x : @SAWCoreScaffolding.Bool), forall (y : @SAWCoreScaffolding.Bool), ((((@SAWCorePrelude.EqTrue) (x))) -> ((@SAWCorePrelude.EqTrue) (y))) -> ((@SAWCorePrelude.EqTrue) (((@SAWCorePrelude.implies) (x) (y)))) :=
  (fun (x : @SAWCoreScaffolding.Bool) (y : @SAWCoreScaffolding.Bool) => ((@SAWCoreScaffolding.iteDep) ((fun (x : @SAWCoreScaffolding.Bool) => ((((@SAWCorePrelude.EqTrue) (x))) -> ((@SAWCorePrelude.EqTrue) (y))) -> ((@SAWCorePrelude.EqTrue) (((@SAWCorePrelude.implies) (x) (y)))))) (x) ((fun (H : (((@Eq) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.True) (@SAWCoreScaffolding.True))) -> ((@Eq) (@SAWCoreScaffolding.Bool) (y) (@SAWCoreScaffolding.True))) => ((@SAWCorePrelude.trans) (@SAWCoreScaffolding.Bool) (((@SAWCorePrelude.implies) (@SAWCoreScaffolding.True) (y))) (y) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.implies_True1) (y))) (((H) (@SAWCorePrelude.TrueI)))))) ((fun (_ : (((@Eq) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.False) (@SAWCoreScaffolding.True))) -> ((@Eq) (@SAWCoreScaffolding.Bool) (y) (@SAWCoreScaffolding.True))) => ((@SAWCorePrelude.implies_False1) (y)))))).

(* Prelude.eq was skipped *)

(* Prelude.eq_refl was skipped *)

(* Prelude.eq_Bool was skipped *)

(* Prelude.ite_eq_cong_1 was skipped *)

(* Prelude.ite_eq_cong_2 was skipped *)

Inductive Either (s : Type) (t : Type) : Type :=
| Left : (s) -> ((@Either) (s) (t))
| Right : (t) -> ((@Either) (s) (t))
.

Definition Either__rec : forall (s : Type), forall (t : Type), forall (p : (((@Either) (s) (t))) -> Type), (forall (l : s), ((p) (((@Left) (s) (t) (l))))) -> (forall (r : t), ((p) (((@Right) (s) (t) (r))))) -> forall (e : ((@Either) (s) (t))), ((p) (e)) :=
  (fun (s : Type) (t : Type) (p : (((@Either) (s) (t))) -> Type) (f1 : forall (l : s), ((p) (((@Left) (s) (t) (l))))) (f2 : forall (r : t), ((p) (((@Right) (s) (t) (r))))) (e : ((@Either) (s) (t))) => ((@Either_rect) (s) (t) (p) (f1) (f2) (e))).

Definition either : forall (a : Type), forall (b : Type), forall (c : Type), ((a) -> c) -> ((b) -> c) -> (((@Either) (a) (b))) -> c :=
  (fun (a : Type) (b : Type) (c : Type) (f : (a) -> c) (g : (b) -> c) (e : ((@Either) (a) (b))) => ((@SAWCorePrelude.Either__rec) (a) (b) ((fun (p : ((@Either) (a) (b))) => c)) (f) (g) (e))).

Definition eitherCong0 : forall (t : Type), forall (x : Type), forall (y : Type), (((@Eq) (Type) (x) (y))) -> ((@Eq) (Type) (((@Either) (x) (t))) (((@Either) (y) (t)))) :=
  (fun (t : Type) (x : Type) (y : Type) (eq : ((@Eq) (Type) (x) (y))) => ((@SAWCorePrelude.eq_cong) (Type) (x) (y) (eq) (Type) ((fun (y' : Type) => ((@Either) (y') (t)))))).

Definition eitherCong1 : forall (t : Type), forall (x : Type), forall (y : Type), (((@Eq) (Type) (x) (y))) -> ((@Eq) (Type) (((@Either) (t) (x))) (((@Either) (t) (y)))) :=
  (fun (t : Type) (x : Type) (y : Type) (eq : ((@Eq) (Type) (x) (y))) => ((@SAWCorePrelude.eq_cong) (Type) (x) (y) (eq) (Type) ((fun (y' : Type) => ((@Either) (t) (y')))))).

Inductive Maybe (a : Type) : Type :=
| Nothing :  ((@Maybe) (a))
| Just : (a) -> ((@Maybe) (a))
.

Definition Maybe__rec : forall (a : Type), forall (p : (((@Maybe) (a))) -> Type), (((p) (((@Nothing) (a))))) -> (forall (x : a), ((p) (((@Just) (a) (x))))) -> forall (m : ((@Maybe) (a))), ((p) (m)) :=
  (fun (a : Type) (p : (((@Maybe) (a))) -> Type) (f1 : ((p) (((@Nothing) (a))))) (f2 : forall (x : a), ((p) (((@Just) (a) (x))))) (m : ((@Maybe) (a))) => ((@Maybe_rect) (a) (p) (f1) (f2) (m))).

Definition maybe : forall (a : Type), forall (b : Type), (b) -> ((a) -> b) -> (((@Maybe) (a))) -> b :=
  (fun (a : Type) (b : Type) (f1 : b) (f2 : (a) -> b) (m : ((@Maybe) (a))) => ((@SAWCorePrelude.Maybe__rec) (a) ((fun (m' : ((@Maybe) (a))) => b)) (f1) (f2) (m))).

(* Prelude.Nat was skipped *)

Definition Nat__rec : forall (p : (((@Nat))) -> Type), (((p) (((@Zero))))) -> (forall (n : ((@Nat))), (((p) (n))) -> ((p) (((@Succ) (n))))) -> forall (n : ((@Nat))), ((p) (n)) :=
  (fun (p : (((@Nat))) -> Type) (f1 : ((p) (0))) (f2 : forall (n : ((@Nat))), (((p) (n))) -> ((p) (((@Succ) (n))))) (n : ((@Nat))) => ((@Nat_rect) (p) (f1) (f2) (n))).

Definition Nat_cases : forall (a : Type), (a) -> ((((@Nat))) -> (a) -> a) -> (((@Nat))) -> a :=
  (fun (a : Type) (f1 : a) (f2 : (((@Nat))) -> (a) -> a) (n : ((@Nat))) => ((@SAWCorePrelude.Nat__rec) ((fun (n : ((@Nat))) => a)) (f1) (f2) (n))).

Definition Nat_cases2 : forall (a : Type), ((((@Nat))) -> a) -> ((((@Nat))) -> a) -> ((((@Nat))) -> (((@Nat))) -> (a) -> a) -> (((@Nat))) -> (((@Nat))) -> a :=
  (fun (a : Type) (f1 : (((@Nat))) -> a) (f2 : (((@Nat))) -> a) (f3 : (((@Nat))) -> (((@Nat))) -> (a) -> a) (n : ((@Nat))) (m : ((@Nat))) => ((@SAWCorePrelude.Nat__rec) ((fun (n : ((@Nat))) => (((@Nat))) -> a)) (f1) ((fun (n : ((@Nat))) (f_rec : (((@Nat))) -> a) (m : ((@Nat))) => ((@SAWCorePrelude.Nat__rec) ((fun (m' : ((@Nat))) => a)) (((f2) (n))) ((fun (m' : ((@Nat))) (frec' : a) => ((f3) (n) (m') (((f_rec) (m')))))) (m)))) (n) (m))).

Definition eqNat : (((@Nat))) -> (((@Nat))) -> Type :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((@Eq) (((@Nat))) (x) (y))).

Definition eqNatSucc : forall (x : ((@Nat))), forall (y : ((@Nat))), (((@SAWCorePrelude.eqNat) (x) (y))) -> ((@SAWCorePrelude.eqNat) (((@Succ) (x))) (((@Succ) (y)))) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) (eq : ((@Eq) (((@Nat))) (x) (y))) => ((@SAWCorePrelude.eq_cong) (((@Nat))) (x) (y) (eq) (((@Nat))) ((fun (n : ((@Nat))) => ((@Succ) (n)))))).

Definition pred : (((@Nat))) -> ((@Nat)) :=
  (fun (x : ((@Nat))) => ((@SAWCorePrelude.Nat_cases) (((@Nat))) (((@Zero))) ((fun (n : ((@Nat))) (m : ((@Nat))) => n)) (x))).

Definition eqNatPrec : forall (x : ((@Nat))), forall (y : ((@Nat))), (((@SAWCorePrelude.eqNat) (((@Succ) (x))) (((@Succ) (y))))) -> ((@SAWCorePrelude.eqNat) (x) (y)) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) (eq' : ((@Eq) (((@Nat))) (((@Succ) (x))) (((@Succ) (y))))) => ((@SAWCorePrelude.eq_cong) (((@Nat))) (((@Succ) (x))) (((@Succ) (y))) (eq') (((@Nat))) (@SAWCorePrelude.pred))).

Definition addNat : (((@Nat))) -> (((@Nat))) -> ((@Nat)) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((@SAWCorePrelude.Nat_cases) (((@Nat))) (y) ((fun (_ : ((@Nat))) (prev_sum : ((@Nat))) => ((@Succ) (prev_sum)))) (x))).

Definition eqNatAdd0 : forall (x : ((@Nat))), ((@SAWCorePrelude.eqNat) (((@SAWCorePrelude.addNat) (x) (0))) (x)) :=
  (fun (x : ((@Nat))) => ((@SAWCorePrelude.Nat__rec) ((fun (n : ((@Nat))) => ((@SAWCorePrelude.eqNat) (((@SAWCorePrelude.addNat) (n) (0))) (n)))) (((@Refl) (((@Nat))) (0))) ((fun (n : ((@Nat))) => ((@SAWCorePrelude.eqNatSucc) (((@SAWCorePrelude.addNat) (n) (0))) (n)))) (x))).

Definition eqNatAddS : forall (x : ((@Nat))), forall (y : ((@Nat))), ((@SAWCorePrelude.eqNat) (((@SAWCorePrelude.addNat) (x) (((@Succ) (y))))) (((@Succ) (((@SAWCorePrelude.addNat) (x) (y)))))) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((@SAWCorePrelude.Nat__rec) ((fun (x' : ((@Nat))) => forall (y' : ((@Nat))), ((@SAWCorePrelude.eqNat) (((@SAWCorePrelude.addNat) (x') (((@Succ) (y'))))) (((@Succ) (((@SAWCorePrelude.addNat) (x') (y')))))))) ((fun (y' : ((@Nat))) => ((@Refl) (((@Nat))) (((@Succ) (y')))))) ((fun (x' : ((@Nat))) (eqF : forall (y' : ((@Nat))), ((@Eq) (((@Nat))) (((@Nat_rect) ((fun (n : ((@Nat))) => ((@Nat)))) (((@Succ) (y'))) ((fun (_ : ((@Nat))) (prev_sum : ((@Nat))) => ((@Succ) (prev_sum)))) (x'))) (((@Succ) (((@SAWCorePrelude.addNat) (x') (y'))))))) (y' : ((@Nat))) => ((@SAWCorePrelude.eqNatSucc) (((@SAWCorePrelude.addNat) (x') (((@Succ) (y'))))) (((@Succ) (((@SAWCorePrelude.addNat) (x') (y'))))) (((eqF) (y')))))) (x) (y))).

Definition eqNatAddComm : forall (x : ((@Nat))), forall (y : ((@Nat))), ((@SAWCorePrelude.eqNat) (((@SAWCorePrelude.addNat) (x) (y))) (((@SAWCorePrelude.addNat) (y) (x)))) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((@SAWCorePrelude.Nat__rec) ((fun (y' : ((@Nat))) => forall (x' : ((@Nat))), ((@SAWCorePrelude.eqNat) (((@SAWCorePrelude.addNat) (x') (y'))) (((@SAWCorePrelude.addNat) (y') (x')))))) ((fun (x' : ((@Nat))) => ((@SAWCorePrelude.eqNatAdd0) (x')))) ((fun (y' : ((@Nat))) (eqF : forall (x' : ((@Nat))), ((@Eq) (((@Nat))) (((@Nat_rect) ((fun (n : ((@Nat))) => ((@Nat)))) (y') ((fun (_ : ((@Nat))) (prev_sum : ((@Nat))) => ((@Succ) (prev_sum)))) (x'))) (((@Nat_rect) ((fun (n : ((@Nat))) => ((@Nat)))) (x') ((fun (_ : ((@Nat))) (prev_sum : ((@Nat))) => ((@Succ) (prev_sum)))) (y'))))) (x' : ((@Nat))) => ((@SAWCorePrelude.trans) (((@Nat))) (((@SAWCorePrelude.addNat) (x') (((@Succ) (y'))))) (((@Succ) (((@SAWCorePrelude.addNat) (x') (y'))))) (((@Succ) (((@SAWCorePrelude.addNat) (y') (x'))))) (((@SAWCorePrelude.eqNatAddS) (x') (y'))) (((@SAWCorePrelude.eqNatSucc) (((@SAWCorePrelude.addNat) (x') (y'))) (((@SAWCorePrelude.addNat) (y') (x'))) (((eqF) (x')))))))) (y) (x))).

Definition addNat_assoc : forall (x : ((@Nat))), forall (y : ((@Nat))), forall (z : ((@Nat))), ((@SAWCorePrelude.eqNat) (((@SAWCorePrelude.addNat) (x) (((@SAWCorePrelude.addNat) (y) (z))))) (((@SAWCorePrelude.addNat) (((@SAWCorePrelude.addNat) (x) (y))) (z)))) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) (z : ((@Nat))) => ((@SAWCorePrelude.Nat__rec) ((fun (x' : ((@Nat))) => ((@SAWCorePrelude.eqNat) (((@SAWCorePrelude.addNat) (x') (((@SAWCorePrelude.addNat) (y) (z))))) (((@SAWCorePrelude.addNat) (((@SAWCorePrelude.addNat) (x') (y))) (z)))))) (((@Refl) (((@Nat))) (((@SAWCorePrelude.addNat) (y) (z))))) ((fun (x' : ((@Nat))) (eq : ((@Eq) (((@Nat))) (((@Nat_rect) ((fun (n : ((@Nat))) => ((@Nat)))) (((@SAWCorePrelude.addNat) (y) (z))) ((fun (_ : ((@Nat))) (prev_sum : ((@Nat))) => ((@Succ) (prev_sum)))) (x'))) (((@Nat_rect) ((fun (n : ((@Nat))) => ((@Nat)))) (z) ((fun (_ : ((@Nat))) (prev_sum : ((@Nat))) => ((@Succ) (prev_sum)))) (((@Nat_rect) ((fun (n : ((@Nat))) => ((@Nat)))) (y) ((fun (_ : ((@Nat))) (prev_sum : ((@Nat))) => ((@Succ) (prev_sum)))) (x'))))))) => ((@SAWCorePrelude.eqNatSucc) (((@SAWCorePrelude.addNat) (x') (((@SAWCorePrelude.addNat) (y) (z))))) (((@SAWCorePrelude.addNat) (((@SAWCorePrelude.addNat) (x') (y))) (z))) (eq)))) (x))).

Definition mulNat : (((@Nat))) -> (((@Nat))) -> ((@Nat)) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((@SAWCorePrelude.Nat__rec) ((fun (x' : ((@Nat))) => ((@Nat)))) (0) ((fun (x' : ((@Nat))) (prod : ((@Nat))) => ((@SAWCorePrelude.addNat) (y) (prod)))) (x))).

Definition equal0Nat : (((@Nat))) -> @SAWCoreScaffolding.Bool :=
  (fun (n : ((@Nat))) => ((@SAWCorePrelude.Nat_cases) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.True) ((fun (n : ((@Nat))) (b : @SAWCoreScaffolding.Bool) => @SAWCoreScaffolding.False)) (n))).

Definition equalNat : (((@Nat))) -> (((@Nat))) -> @SAWCoreScaffolding.Bool :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((@SAWCorePrelude.Nat_cases) ((((@Nat))) -> @SAWCoreScaffolding.Bool) (@SAWCorePrelude.equal0Nat) ((fun (n' : ((@Nat))) (eqN : (((@Nat))) -> @SAWCoreScaffolding.Bool) (m : ((@Nat))) => ((@SAWCorePrelude.Nat_cases) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.False) ((fun (m' : ((@Nat))) (b : @SAWCoreScaffolding.Bool) => ((eqN) (m')))) (m)))) (x) (y))).

Definition ltNat : (((@Nat))) -> (((@Nat))) -> @SAWCoreScaffolding.Bool :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((@SAWCorePrelude.Nat_cases2) (@SAWCoreScaffolding.Bool) ((fun (x' : ((@Nat))) => @SAWCoreScaffolding.False)) ((fun (y' : ((@Nat))) => @SAWCoreScaffolding.True)) ((fun (y' : ((@Nat))) (x' : ((@Nat))) (lt_mn : @SAWCoreScaffolding.Bool) => lt_mn)) (y) (x))).

Definition subNat : (((@Nat))) -> (((@Nat))) -> ((@Nat)) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((@SAWCorePrelude.Nat_cases2) (((@Nat))) ((fun (x' : ((@Nat))) => x')) ((fun (y' : ((@Nat))) => ((@Zero)))) ((fun (y' : ((@Nat))) (x' : ((@Nat))) (sub_xy : ((@Nat))) => sub_xy)) (y) (x))).

Definition minNat : (((@Nat))) -> (((@Nat))) -> ((@Nat)) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((@SAWCorePrelude.Nat_cases2) (((@Nat))) ((fun (y' : ((@Nat))) => ((@Zero)))) ((fun (x' : ((@Nat))) => ((@Zero)))) ((fun (x' : ((@Nat))) (y' : ((@Nat))) (min_xy : ((@Nat))) => ((@Succ) (min_xy)))) (x) (y))).

Definition maxNat : (((@Nat))) -> (((@Nat))) -> ((@Nat)) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((@SAWCorePrelude.Nat_cases2) (((@Nat))) ((fun (x' : ((@Nat))) => x')) ((fun (y' : ((@Nat))) => ((@Succ) (y')))) ((fun (y' : ((@Nat))) (x' : ((@Nat))) (sub_xy : ((@Nat))) => sub_xy)) (y) (x))).

(* Prelude.widthNat was skipped *)

(* Prelude.eq_Nat was skipped *)

Definition expNat : (((@Nat))) -> (((@Nat))) -> ((@Nat)) :=
  (fun (b : ((@Nat))) (e : ((@Nat))) => ((@SAWCorePrelude.Nat_cases) (((@Nat))) (1) ((fun (e' : ((@Nat))) (exp_b_e : ((@Nat))) => ((@SAWCorePrelude.mulNat) (b) (exp_b_e)))) (e))).

(* Prelude.divModNat was skipped *)

Definition divNat : (((@Nat))) -> (((@Nat))) -> ((@Nat)) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((fst) (((@SAWCoreScaffolding.divModNat) (x) (y))))).

Definition modNat : (((@Nat))) -> (((@Nat))) -> ((@Nat)) :=
  (fun (x : ((@Nat))) (y : ((@Nat))) => ((snd) (((@SAWCoreScaffolding.divModNat) (x) (y))))).

Definition natCase : forall (p : (((@Nat))) -> Type), (((p) (((@Zero))))) -> (forall (n : ((@Nat))), ((p) (((@Succ) (n))))) -> forall (n : ((@Nat))), ((p) (n)) :=
  (fun (p : (((@Nat))) -> Type) (z : ((p) (0))) (s : forall (n : ((@Nat))), ((p) (((@Succ) (n))))) => ((@SAWCorePrelude.Nat__rec) (p) (z) ((fun (n : ((@Nat))) (r : ((p) (n))) => ((s) (n)))))).

Definition if0Nat : forall (a : Type), (((@Nat))) -> (a) -> (a) -> a :=
  (fun (a : Type) (n : ((@Nat))) (x : a) (y : a) => ((@SAWCorePrelude.natCase) ((fun (_ : ((@Nat))) => a)) (x) ((fun (_ : ((@Nat))) => y)) (n))).

(* Prelude.Vec was skipped *)

(* Prelude.gen was skipped *)

(* Prelude.atWithDefault was skipped *)

Definition sawAt : forall (n : ((@Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@Nat))) -> a :=
  (fun (n : ((@Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@Nat))) => ((@SAWCoreVectorsAsCoqVectors.atWithDefault) (n) (a) (((@SAWCoreScaffolding.error) (a) (("at: index out of bounds")%string))) (v) (i))).

(* Prelude.EmptyVec was skipped *)

Definition ConsVec : forall (a : Type), (a) -> forall (n : ((@Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (((@Succ) (n))) (a)) :=
  (fun (a : Type) (x : a) (n : ((@Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (((@Succ) (n))) (a) (((@SAWCorePrelude.Nat_cases) (a) (x) ((fun (i : ((@Nat))) (a' : a) => ((@SAWCorePrelude.sawAt) (n) (a) (v) (i)))))))).

Definition upd : forall (n : ((@Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@Nat))) -> (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (j : ((@Nat))) (x : a) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (i : ((@Nat))) => if ((@SAWCorePrelude.equalNat) (i) (j)) then x else ((@SAWCorePrelude.sawAt) (n) (a) (v) (i)))))).

Definition map : forall (a : Type), forall (b : Type), ((a) -> b) -> forall (n : ((@Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (b)) :=
  (fun (a : Type) (b : Type) (f : (a) -> b) (n : ((@Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (b) ((fun (i : ((@Nat))) => ((f) (((@SAWCorePrelude.sawAt) (n) (a) (v) (i)))))))).

Definition zipWith : forall (a : Type), forall (b : Type), forall (c : Type), ((a) -> (b) -> c) -> forall (n : ((@Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (b))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (c)) :=
  (fun (a : Type) (b : Type) (c : Type) (f : (a) -> (b) -> c) (n : ((@Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (b))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (c) ((fun (i : ((@Nat))) => ((f) (((@SAWCorePrelude.sawAt) (n) (a) (x) (i))) (((@SAWCorePrelude.sawAt) (n) (b) (y) (i)))))))).

Definition replicate : forall (n : ((@Nat))), forall (a : Type), (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@Nat))) (a : Type) (x : a) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (_ : ((@Nat))) => x)))).

Definition single : forall (a : Type), (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (1) (a)) :=
  ((@SAWCorePrelude.replicate) (1)).

(* Prelude.at_single was skipped *)


Fixpoint zip (a b : sort 0) (m n : Nat) (xs : Vec m a) (ys : Vec n b)
  : Vec (minNat m n) (a * b) :=
  match
    xs in Vector.t _ m'
    return Vector.t _ (minNat m' n)
  with
  | Vector.nil => Vector.nil _
  | Vector.cons x pm xs =>
    match
      ys in Vector.t _ n'
      return Vector.t _ (minNat (S pm) n')
    with
    | Vector.nil => Vector.nil _
    | Vector.cons y pm' ys => Vector.cons _ (x, y) _ (zip _ _ _ _ xs ys)
    end
  end
.

(* Prelude.foldr was skipped *)

Definition reverse : forall (n : ((@Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@Nat))) (a : Type) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (i : ((@Nat))) => ((@SAWCorePrelude.sawAt) (n) (a) (xs) (((@SAWCorePrelude.subNat) (((@SAWCorePrelude.subNat) (n) (1))) (i)))))))).

Definition transpose : forall (m : ((@Nat))), forall (n : ((@Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a)))) :=
  (fun (m : ((@Nat))) (n : ((@Nat))) (a : Type) (xss : ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) ((fun (j : ((@Nat))) => ((@SAWCoreVectorsAsCoqVectors.gen) (m) (a) ((fun (i : ((@Nat))) => ((@SAWCorePrelude.sawAt) (n) (a) (((@SAWCorePrelude.sawAt) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (xss) (i))) (j))))))))).

Definition vecEq : forall (n : ((@Nat))), forall (a : Type), ((a) -> (a) -> @SAWCoreScaffolding.Bool) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> @SAWCoreScaffolding.Bool :=
  (fun (n : ((@Nat))) (a : Type) (eqFn : (a) -> (a) -> @SAWCoreScaffolding.Bool) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) => ((@SAWCoreVectorsAsCoqVectors.foldr) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.Bool) (n) (@SAWCoreScaffolding.and) (@SAWCoreScaffolding.True) (((@SAWCorePrelude.zipWith) (a) (a) (@SAWCoreScaffolding.Bool) (eqFn) (n) (x) (y))))).

(* Prelude.eq_Vec was skipped *)

Definition take : forall (a : Type), forall (m : ((@Nat))), forall (n : ((@Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.addNat) (m) (n))) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a)) :=
  (fun (a : Type) (m : ((@Nat))) (n : ((@Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.addNat) (m) (n))) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (m) (a) ((fun (i : ((@Nat))) => ((@SAWCorePrelude.sawAt) (((@SAWCorePrelude.addNat) (m) (n))) (a) (v) (i)))))).

Definition vecCong : forall (a : Type), forall (m : ((@Nat))), forall (n : ((@Nat))), (((@Eq) (((@Nat))) (m) (n))) -> ((@Eq) (Type) (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (a : Type) (m : ((@Nat))) (n : ((@Nat))) (eq : ((@Eq) (((@Nat))) (m) (n))) => ((@SAWCorePrelude.eq_cong) (((@Nat))) (m) (n) (eq) (Type) ((fun (i : ((@Nat))) => ((@SAWCoreVectorsAsCoqVectors.Vec) (i) (a)))))).

(* Prelude.coerceVec was skipped *)

(* Prelude.take0 was skipped *)

Definition drop : forall (a : Type), forall (m : ((@Nat))), forall (n : ((@Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.addNat) (m) (n))) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (a : Type) (m : ((@Nat))) (n : ((@Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.addNat) (m) (n))) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (i : ((@Nat))) => ((@SAWCorePrelude.sawAt) (((@SAWCorePrelude.addNat) (m) (n))) (a) (v) (((@SAWCorePrelude.addNat) (m) (i)))))))).

(* Prelude.drop0 was skipped *)

Definition slice : forall (a : Type), forall (m : ((@Nat))), forall (n : ((@Nat))), forall (o : ((@Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.addNat) (((@SAWCorePrelude.addNat) (m) (n))) (o))) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (a : Type) (m : ((@Nat))) (n : ((@Nat))) (o : ((@Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.addNat) (((@SAWCorePrelude.addNat) (m) (n))) (o))) (a))) => ((@SAWCorePrelude.drop) (a) (m) (n) (((@SAWCorePrelude.take) (a) (((@SAWCorePrelude.addNat) (m) (n))) (o) (v))))).

Definition join : forall (m : ((@Nat))), forall (n : ((@Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.mulNat) (m) (n))) (a)) :=
  (fun (m : ((@Nat))) (n : ((@Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) => ((@SAWCoreVectorsAsCoqVectors.gen) (((@SAWCorePrelude.mulNat) (m) (n))) (a) ((fun (i : ((@Nat))) => ((@SAWCorePrelude.sawAt) (n) (a) (((@SAWCorePrelude.sawAt) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (v) (((@SAWCorePrelude.divNat) (i) (n))))) (((@SAWCorePrelude.modNat) (i) (n)))))))).

Definition split : forall (m : ((@Nat))), forall (n : ((@Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.mulNat) (m) (n))) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (m : ((@Nat))) (n : ((@Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.mulNat) (m) (n))) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) ((fun (i : ((@Nat))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (j : ((@Nat))) => ((@SAWCorePrelude.sawAt) (((@SAWCorePrelude.mulNat) (m) (n))) (a) (v) (((@SAWCorePrelude.addNat) (((@SAWCorePrelude.mulNat) (i) (n))) (j))))))))))).

Definition append : forall (m : ((@Nat))), forall (n : ((@Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.addNat) (m) (n))) (a)) :=
  (fun (m : ((@Nat))) (n : ((@Nat))) (a : Type) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (((@SAWCorePrelude.addNat) (m) (n))) (a) ((fun (i : ((@Nat))) => if ((@SAWCorePrelude.ltNat) (i) (m)) then ((@SAWCorePrelude.sawAt) (m) (a) (x) (i)) else ((@SAWCorePrelude.sawAt) (n) (a) (y) (((@SAWCorePrelude.subNat) (i) (m)))))))).

(* Prelude.rotateL was skipped *)

(* Prelude.rotateR was skipped *)

(* Prelude.shiftL was skipped *)

(* Prelude.shiftR was skipped *)

Definition joinLittleEndian : forall (m : ((@Nat))), forall (n : ((@Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.mulNat) (m) (n))) (a)) :=
  (fun (m : ((@Nat))) (n : ((@Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) => ((@SAWCorePrelude.join) (m) (n) (a) (((@SAWCorePrelude.reverse) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (v))))).

Definition splitLittleEndian : forall (m : ((@Nat))), forall (n : ((@Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.mulNat) (m) (n))) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (m : ((@Nat))) (n : ((@Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.mulNat) (m) (n))) (a))) => ((@SAWCorePrelude.reverse) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (((@SAWCorePrelude.split) (m) (n) (a) (v))))).

Definition bitvector : forall (n : ((@Nat))), Type :=
  (fun (n : ((@Nat))) => ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))).

Definition msb : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (((@Succ) (n))))) -> @SAWCoreScaffolding.Bool :=
  (fun (n : ((@Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@Succ) (n))) (@SAWCoreScaffolding.Bool))) => ((@SAWCorePrelude.sawAt) (((@Succ) (n))) (@SAWCoreScaffolding.Bool) (v) (0))).

Definition lsb : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (((@Succ) (n))))) -> @SAWCoreScaffolding.Bool :=
  (fun (n : ((@Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@Succ) (n))) (@SAWCoreScaffolding.Bool))) => ((@SAWCorePrelude.sawAt) (((@Succ) (n))) (@SAWCoreScaffolding.Bool) (v) (n))).

(* Prelude.bvNat was skipped *)

(* Prelude.bvToNat was skipped *)

Definition bvAt : forall (n : ((@Nat))), forall (a : Type), forall (w : ((@Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCorePrelude.bitvector) (w))) -> a :=
  (fun (n : ((@Nat))) (a : Type) (w : ((@Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (@SAWCoreScaffolding.Bool))) => ((@SAWCorePrelude.sawAt) (n) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

Definition bvUpd : forall (n : ((@Nat))), forall (a : Type), forall (w : ((@Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCorePrelude.bitvector) (w))) -> (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@Nat))) (a : Type) (w : ((@Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (@SAWCoreScaffolding.Bool))) (y : a) => ((@SAWCorePrelude.upd) (n) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))) (y))).

Definition bvRotateL : forall (n : ((@Nat))), forall (a : Type), forall (w : ((@Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCorePrelude.bitvector) (w))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@Nat))) (a : Type) (w : ((@Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (@SAWCoreScaffolding.Bool))) => ((@SAWCoreVectorsAsCoqVectors.rotateL) (n) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

Definition bvRotateR : forall (n : ((@Nat))), forall (a : Type), forall (w : ((@Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCorePrelude.bitvector) (w))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@Nat))) (a : Type) (w : ((@Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (@SAWCoreScaffolding.Bool))) => ((@SAWCoreVectorsAsCoqVectors.rotateR) (n) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

Definition bvShiftL : forall (n : ((@Nat))), forall (a : Type), forall (w : ((@Nat))), (a) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCorePrelude.bitvector) (w))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@Nat))) (a : Type) (w : ((@Nat))) (z : a) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (@SAWCoreScaffolding.Bool))) => ((@SAWCoreVectorsAsCoqVectors.shiftL) (n) (a) (z) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

Definition bvShiftR : forall (n : ((@Nat))), forall (a : Type), forall (w : ((@Nat))), (a) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCorePrelude.bitvector) (w))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@Nat))) (a : Type) (w : ((@Nat))) (z : a) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (@SAWCoreScaffolding.Bool))) => ((@SAWCoreVectorsAsCoqVectors.shiftR) (n) (a) (z) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

(* Prelude.bvAdd was skipped *)

(* Prelude.bvugt was skipped *)

(* Prelude.bvuge was skipped *)

(* Prelude.bvult was skipped *)

(* Prelude.bvule was skipped *)

(* Prelude.bvsgt was skipped *)

(* Prelude.bvsge was skipped *)

(* Prelude.bvslt was skipped *)

(* Prelude.bvsle was skipped *)

(* Prelude.bvPopcount was skipped *)

(* Prelude.bvCountLeadingZeros was skipped *)

(* Prelude.bvCountTrailingZeros was skipped *)

(* Prelude.bvForall was skipped *)

Definition bvCarry : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCorePrelude.bitvector) (n))) -> @SAWCoreScaffolding.Bool :=
  (fun (n : ((@Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) => ((@SAWCoreVectorsAsCoqVectors.bvult) (n) (((@SAWCoreVectorsAsCoqVectors.bvAdd) (n) (x) (y))) (x))).

Definition bvSCarry : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (((@Succ) (n))))) -> (((@SAWCorePrelude.bitvector) (((@Succ) (n))))) -> @SAWCoreScaffolding.Bool :=
  (fun (n : ((@Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@Succ) (n))) (@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@Succ) (n))) (@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.boolEq) (((@SAWCorePrelude.msb) (n) (x))) (((@SAWCorePrelude.msb) (n) (y))))) (((@SAWCoreScaffolding.xor) (((@SAWCorePrelude.msb) (n) (x))) (((@SAWCorePrelude.msb) (n) (((@SAWCoreVectorsAsCoqVectors.bvAdd) (((@Succ) (n))) (x) (y))))))))).

Definition bvAddWithCarry : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCorePrelude.bitvector) (n))) -> ((prod) (@SAWCoreScaffolding.Bool) (((@SAWCorePrelude.bitvector) (n)))) :=
  (fun (n : ((@Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) => ((pair) (((@SAWCorePrelude.bvCarry) (n) (x) (y))) (((@SAWCoreVectorsAsCoqVectors.bvAdd) (n) (x) (y))))).

(* Prelude.bvAddZeroL was skipped *)

(* Prelude.bvAddZeroR was skipped *)

(* Prelude.bvNeg was skipped *)

(* Prelude.bvSub was skipped *)

(* Prelude.bvMul was skipped *)

(* Prelude.bvLg2 was skipped *)

(* Prelude.bvUDiv was skipped *)

(* Prelude.bvURem was skipped *)

(* Prelude.bvSDiv was skipped *)

(* Prelude.bvSRem was skipped *)

(* Prelude.bvShl was skipped *)

(* Prelude.bvShr was skipped *)

(* Prelude.bvSShr was skipped *)

(* Prelude.bvShiftL_bvShl was skipped *)

(* Prelude.bvShiftR_bvShr was skipped *)

Definition bvZipWith : ((@SAWCoreScaffolding.Bool) -> (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool) -> forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCorePrelude.bitvector) (n))) -> ((@SAWCorePrelude.bitvector) (n)) :=
  ((@SAWCorePrelude.zipWith) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.Bool)).

Definition bvNot : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> ((@SAWCorePrelude.bitvector) (n)) :=
  ((@SAWCorePrelude.map) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.not)).

Definition bvAnd : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCorePrelude.bitvector) (n))) -> ((@SAWCorePrelude.bitvector) (n)) :=
  ((@SAWCorePrelude.bvZipWith) (@SAWCoreScaffolding.and)).

Definition bvOr : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCorePrelude.bitvector) (n))) -> ((@SAWCorePrelude.bitvector) (n)) :=
  ((@SAWCorePrelude.bvZipWith) (@SAWCoreScaffolding.or)).

Definition bvXor : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCorePrelude.bitvector) (n))) -> ((@SAWCorePrelude.bitvector) (n)) :=
  ((@SAWCorePrelude.bvZipWith) (@SAWCoreScaffolding.xor)).

Definition bvEq : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCorePrelude.bitvector) (n))) -> @SAWCoreScaffolding.Bool :=
  (fun (n : ((@Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) => ((@SAWCorePrelude.vecEq) (n) (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.boolEq) (x) (y))).

(* Prelude.bvEq_refl was skipped *)

(* Prelude.eq_bitvector was skipped *)

(* Prelude.eq_VecBool was skipped *)

(* Prelude.eq_VecVec was skipped *)

(* Prelude.equalNat_bv was skipped *)

Definition bvBool : forall (n : ((@Nat))), (@SAWCoreScaffolding.Bool) -> ((@SAWCorePrelude.bitvector) (n)) :=
  (fun (n : ((@Nat))) (b : @SAWCoreScaffolding.Bool) => if b then ((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (1)) else ((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (0))).

Definition bvNe : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCorePrelude.bitvector) (n))) -> @SAWCoreScaffolding.Bool :=
  (fun (n : ((@Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.not) (((@SAWCorePrelude.bvEq) (n) (x) (y))))).

Definition bvNonzero : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> @SAWCoreScaffolding.Bool :=
  (fun (n : ((@Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) => ((@SAWCorePrelude.bvNe) (n) (x) (((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (0))))).

Definition bvTrunc : forall (x : ((@Nat))), forall (y : ((@Nat))), (((@SAWCorePrelude.bitvector) (((@SAWCorePrelude.addNat) (x) (y))))) -> ((@SAWCorePrelude.bitvector) (y)) :=
  ((@SAWCorePrelude.drop) (@SAWCoreScaffolding.Bool)).

Definition bvUExt : forall (m : ((@Nat))), forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> ((@SAWCorePrelude.bitvector) (((@SAWCorePrelude.addNat) (m) (n)))) :=
  (fun (m : ((@Nat))) (n : ((@Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) => ((@SAWCorePrelude.append) (m) (n) (@SAWCoreScaffolding.Bool) (((@SAWCoreVectorsAsCoqVectors.bvNat) (m) (0))) (x))).

Definition replicateBool : forall (n : ((@Nat))), (@SAWCoreScaffolding.Bool) -> ((@SAWCorePrelude.bitvector) (n)) :=
  (fun (n : ((@Nat))) (b : @SAWCoreScaffolding.Bool) => if b then ((@SAWCorePrelude.bvNot) (n) (((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (0)))) else ((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (0))).

Definition bvSExt : forall (m : ((@Nat))), forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (((@Succ) (n))))) -> ((@SAWCorePrelude.bitvector) (((@SAWCorePrelude.addNat) (m) (((@Succ) (n)))))) :=
  (fun (m : ((@Nat))) (n : ((@Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@Succ) (n))) (@SAWCoreScaffolding.Bool))) => ((@SAWCorePrelude.append) (m) (((@Succ) (n))) (@SAWCoreScaffolding.Bool) (((@SAWCorePrelude.replicateBool) (m) (((@SAWCorePrelude.msb) (n) (x))))) (x))).

Inductive Stream (a : Type) : Type :=
| MkStream : ((((@Nat))) -> a) -> ((@Stream) (a))
.

Definition Stream__rec : forall (a : Type), forall (p : (((@Stream) (a))) -> Type), (forall (f : (((@Nat))) -> a), ((p) (((@MkStream) (a) (f))))) -> forall (str : ((@Stream) (a))), ((p) (str)) :=
  (fun (a : Type) (p : (((@Stream) (a))) -> Type) (f1 : forall (f : (((@Nat))) -> a), ((p) (((@MkStream) (a) (f))))) (str : ((@Stream) (a))) => ((@Stream_rect) (a) (p) (f1) (str))).

Definition streamUpd : forall (a : Type), (((@Stream) (a))) -> (((@Nat))) -> (a) -> ((@Stream) (a)) :=
  (fun (a : Type) (strm : ((@Stream) (a))) (i : ((@Nat))) (y : a) => ((@SAWCorePrelude.Stream__rec) (a) ((fun (strm' : ((@Stream) (a))) => ((@Stream) (a)))) ((fun (s : (((@Nat))) -> a) => ((@MkStream) (a) ((fun (j : ((@Nat))) => if ((@SAWCorePrelude.equalNat) (i) (j)) then y else ((s) (j))))))) (strm))).

Definition bvStreamUpd : forall (a : Type), forall (w : ((@Nat))), (((@Stream) (a))) -> (((@SAWCorePrelude.bitvector) (w))) -> (a) -> ((@Stream) (a)) :=
  (fun (a : Type) (w : ((@Nat))) (xs : ((@Stream) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (@SAWCoreScaffolding.Bool))) (y : a) => ((@SAWCorePrelude.streamUpd) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))) (y))).

Definition streamGet : forall (a : Type), (((@Stream) (a))) -> (((@Nat))) -> a :=
  (fun (a : Type) (strm : ((@Stream) (a))) (i : ((@Nat))) => ((@SAWCorePrelude.Stream__rec) (a) ((fun (strm' : ((@Stream) (a))) => a)) ((fun (s : (((@Nat))) -> a) => ((s) (i)))) (strm))).

Definition streamConst : forall (a : Type), (a) -> ((@Stream) (a)) :=
  (fun (a : Type) (x : a) => ((@MkStream) (a) ((fun (i : ((@Nat))) => x)))).

Definition streamMap : forall (a : Type), forall (b : Type), ((a) -> b) -> (((@Stream) (a))) -> ((@Stream) (b)) :=
  (fun (a : Type) (b : Type) (f : (a) -> b) (xs : ((@Stream) (a))) => ((@MkStream) (b) ((fun (i : ((@Nat))) => ((f) (((@SAWCorePrelude.streamGet) (a) (xs) (i)))))))).

Definition streamMap2 : forall (a : Type), forall (b : Type), forall (c : Type), ((a) -> (b) -> c) -> (((@Stream) (a))) -> (((@Stream) (b))) -> ((@Stream) (c)) :=
  (fun (a : Type) (b : Type) (c : Type) (f : (a) -> (b) -> c) (xs : ((@Stream) (a))) (ys : ((@Stream) (b))) => ((@MkStream) (c) ((fun (i : ((@Nat))) => ((f) (((@SAWCorePrelude.streamGet) (a) (xs) (i))) (((@SAWCorePrelude.streamGet) (b) (ys) (i)))))))).

Definition streamTake : forall (a : Type), forall (n : ((@Nat))), (((@Stream) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (a : Type) (n : ((@Nat))) (xs : ((@Stream) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (i : ((@Nat))) => ((@SAWCorePrelude.streamGet) (a) (xs) (i)))))).

Definition streamDrop : forall (a : Type), forall (n : ((@Nat))), (((@Stream) (a))) -> ((@Stream) (a)) :=
  (fun (a : Type) (n : ((@Nat))) (xs : ((@Stream) (a))) => ((@MkStream) (a) ((fun (i : ((@Nat))) => ((@SAWCorePrelude.streamGet) (a) (xs) (((@SAWCorePrelude.addNat) (n) (i)))))))).

Definition streamAppend : forall (a : Type), forall (n : ((@Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@Stream) (a))) -> ((@Stream) (a)) :=
  (fun (a : Type) (n : ((@Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (ys : ((@Stream) (a))) => ((@MkStream) (a) ((fun (i : ((@Nat))) => ((@SAWCoreVectorsAsCoqVectors.atWithDefault) (n) (a) (((@SAWCorePrelude.streamGet) (a) (ys) (((@SAWCorePrelude.subNat) (i) (n))))) (xs) (i)))))).

Definition streamJoin : forall (a : Type), forall (n : ((@Nat))), (((@Stream) (((@SAWCoreVectorsAsCoqVectors.Vec) (((@Succ) (n))) (a))))) -> ((@Stream) (a)) :=
  (fun (a : Type) (n : ((@Nat))) (s : ((@Stream) (((@SAWCoreVectorsAsCoqVectors.Vec) (((@Succ) (n))) (a))))) => ((@MkStream) (a) ((fun (i : ((@Nat))) => ((@SAWCorePrelude.sawAt) (((@Succ) (n))) (a) (((@SAWCorePrelude.streamGet) (((@SAWCoreVectorsAsCoqVectors.Vec) (((@Succ) (n))) (a))) (s) (((@SAWCorePrelude.divNat) (i) (((@Succ) (n))))))) (((@SAWCorePrelude.modNat) (i) (((@Succ) (n)))))))))).

Definition streamSplit : forall (a : Type), forall (n : ((@Nat))), (((@Stream) (a))) -> ((@Stream) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (a : Type) (n : ((@Nat))) (xs : ((@Stream) (a))) => ((@MkStream) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) ((fun (i : ((@Nat))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (j : ((@Nat))) => ((@SAWCorePrelude.streamGet) (a) (xs) (((@SAWCorePrelude.addNat) (((@SAWCorePrelude.mulNat) (i) (n))) (j))))))))))).

Definition bvStreamGet : forall (a : Type), forall (w : ((@Nat))), (((@Stream) (a))) -> (((@SAWCorePrelude.bitvector) (w))) -> a :=
  (fun (a : Type) (w : ((@Nat))) (xs : ((@Stream) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (@SAWCoreScaffolding.Bool))) => ((@SAWCorePrelude.streamGet) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

Definition bvStreamShiftL : forall (a : Type), forall (w : ((@Nat))), (((@Stream) (a))) -> (((@SAWCorePrelude.bitvector) (w))) -> ((@Stream) (a)) :=
  (fun (a : Type) (w : ((@Nat))) (xs : ((@Stream) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (@SAWCoreScaffolding.Bool))) => ((@SAWCorePrelude.streamDrop) (a) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))) (xs))).

Definition bvStreamShiftR : forall (a : Type), forall (w : ((@Nat))), (a) -> (((@Stream) (a))) -> (((@SAWCorePrelude.bitvector) (w))) -> ((@Stream) (a)) :=
  (fun (a : Type) (w : ((@Nat))) (x : a) (xs : ((@Stream) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (@SAWCoreScaffolding.Bool))) => ((@SAWCorePrelude.streamAppend) (a) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))) (((@SAWCorePrelude.replicate) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))) (a) (x))) (xs))).

(* Prelude.Integer was skipped *)

(* Prelude.intAdd was skipped *)

(* Prelude.intSub was skipped *)

(* Prelude.intMul was skipped *)

(* Prelude.intDiv was skipped *)

(* Prelude.intMod was skipped *)

(* Prelude.intMin was skipped *)

(* Prelude.intMax was skipped *)

(* Prelude.intNeg was skipped *)

(* Prelude.intAbs was skipped *)

(* Prelude.intEq was skipped *)

(* Prelude.intLe was skipped *)

(* Prelude.intLt was skipped *)

(* Prelude.intToNat was skipped *)

(* Prelude.natToInt was skipped *)

Axiom intToBv : forall (n : ((@Nat))), (@SAWCoreScaffolding.Integer) -> ((@SAWCorePrelude.bitvector) (n)) .

Axiom bvToInt : forall (n : ((@Nat))), (((@SAWCorePrelude.bitvector) (n))) -> @SAWCoreScaffolding.Integer .

(* Prelude.sbvToInt was skipped *)

(* Prelude.IntMod was skipped *)

(* Prelude.toIntMod was skipped *)

(* Prelude.fromIntMod was skipped *)

(* Prelude.intModEq was skipped *)

(* Prelude.intModAdd was skipped *)

(* Prelude.intModSub was skipped *)

(* Prelude.intModMul was skipped *)

(* Prelude.intModNeg was skipped *)

Definition updNatFun : forall (a : Type), ((((@Nat))) -> a) -> (((@Nat))) -> (a) -> (((@Nat))) -> a :=
  (fun (a : Type) (f : (((@Nat))) -> a) (i : ((@Nat))) (v : a) (x : ((@Nat))) => if ((@SAWCorePrelude.equalNat) (i) (x)) then v else ((f) (x))).

Definition updBvFun : forall (n : ((@Nat))), forall (a : Type), ((((@SAWCorePrelude.bitvector) (n))) -> a) -> (((@SAWCorePrelude.bitvector) (n))) -> (a) -> (((@SAWCorePrelude.bitvector) (n))) -> a :=
  (fun (n : ((@Nat))) (a : Type) (f : (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) -> a) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) (v : a) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (@SAWCoreScaffolding.Bool))) => if ((@SAWCorePrelude.bvEq) (n) (i) (x)) then v else ((f) (x))).

(* Prelude.Float was skipped *)

(* Prelude.mkFloat was skipped *)

(* Prelude.Double was skipped *)

(* Prelude.mkDouble was skipped *)

(* Prelude.CompM was skipped *)

(* Prelude.returnM was skipped *)

(* Prelude.bindM was skipped *)

(* Prelude.composeM was skipped *)

(* Prelude.errorM was skipped *)

(* Prelude.catchM was skipped *)

Inductive InputOutputTypes : Type :=
| TypesNil : ((@InputOutputTypes))
| TypesCons : (Type) -> (Type) -> (((@InputOutputTypes))) -> ((@InputOutputTypes))
.

(* Prelude.letRecFuns was skipped *)

(* Prelude.letRecM was skipped *)

(* Prelude.letRecM1 was skipped *)

(* Prelude.fixM was skipped *)

(* Prelude.test_fun0 was skipped *)

(* Prelude.test_fun1 was skipped *)

(* Prelude.test_fun2 was skipped *)

(* Prelude.test_fun3 was skipped *)

(* Prelude.test_fun4 was skipped *)

(* Prelude.test_fun5 was skipped *)

(* Prelude.test_fun6 was skipped *)

(* Prelude.bveq_sameL was skipped *)

(* Prelude.bveq_sameR was skipped *)

(* Prelude.bveq_same2 was skipped *)

(* Prelude.bvNat_bvToNat was skipped *)

(* Prelude.ite_split_cong was skipped *)

(* Prelude.ite_join_cong was skipped *)

(* Prelude.map_map was skipped *)

End SAWCorePrelude.