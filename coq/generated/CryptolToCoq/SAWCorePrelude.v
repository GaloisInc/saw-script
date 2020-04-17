
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From Records      Require Import Records.



Import ListNotations.

Module SAWCorePrelude.

(* Prelude.id was skipped *)

(* Prelude.fix was skipped *)

(* Prelude.UnitType was skipped *)

(* Prelude.UnitType__rec was skipped *)

(* Prelude.PairType was skipped *)

Definition pair_example : forall (a : Type), forall (b : Type), (a) -> (b) -> ((@SAWCoreScaffolding.PairType) (a) (b)) :=
  (fun (a : Type) (b : Type) (x : a) (y : b) => ((@SAWCoreScaffolding.PairValue) (a) (b) (x) (y))).

(* Prelude.Pair__rec was skipped *)

Definition Pair_fst : forall (a : Type), forall (b : Type), (((@SAWCoreScaffolding.PairType) (a) (b))) -> a :=
  (fun (a : Type) (b : Type) => ((@SAWCoreScaffolding.Pair__rec) (a) (b) ((fun (p : ((@SAWCoreScaffolding.PairType) (a) (b))) => a)) ((fun (x : a) (y : b) => x)))).

Definition Pair_snd : forall (a : Type), forall (b : Type), (((@SAWCoreScaffolding.PairType) (a) (b))) -> b :=
  (fun (a : Type) (b : Type) => ((@SAWCoreScaffolding.Pair__rec) (a) (b) ((fun (p : ((@SAWCoreScaffolding.PairType) (a) (b))) => b)) ((fun (x : a) (y : b) => y)))).

(* Prelude.fst was skipped *)

(* Prelude.snd was skipped *)

Definition uncurry : forall (a : Type), forall (b : Type), forall (c : Type), forall (f : (a) -> (b) -> c), (((prod) (a) (b))) -> c :=
  (fun (a : Type) (b : Type) (c : Type) (f : (a) -> (b) -> c) (x : ((prod) (a) (b))) => ((f) (((SAWCoreScaffolding.fst) (x))) (((SAWCoreScaffolding.snd) (x))))).

(* Prelude.String was skipped *)

(* Prelude.error was skipped *)

(* Prelude.EmptyType was skipped *)

(* Prelude.EmptyType__rec was skipped *)

(* Prelude.RecordType was skipped *)

(* Prelude.RecordType__rec was skipped *)

(* Prelude.Eq was skipped *)

(* Prelude.EqP was skipped *)

(* Prelude.Eq__rec was skipped *)

Definition eq_cong : forall (t : Type), forall (x : t), forall (y : t), (((@SAWCoreScaffolding.Eq) (t) (x) (y))) -> forall (u : Type), forall (f : (t) -> u), ((@SAWCoreScaffolding.Eq) (u) (((f) (x))) (((f) (y)))) :=
  (fun (t : Type) (x : t) (y : t) (eq : ((@SAWCoreScaffolding.Eq) (t) (x) (y))) (u : Type) (f : (t) -> u) => ((@SAWCoreScaffolding.Eq__rec) (t) (x) ((fun (y' : t) (eq' : ((@SAWCoreScaffolding.Eq) (t) (x) (y'))) => ((@SAWCoreScaffolding.Eq) (u) (((f) (x))) (((f) (y')))))) (((@SAWCoreScaffolding.Refl) (u) (((f) (x))))) (y) (eq))).

(* Prelude.EqP__rec was skipped *)

Definition eqP_cong : forall (t : Type), forall (x : t), forall (y : t), (((@SAWCoreScaffolding.EqP) (t) (x) (y))) -> forall (u : Type), forall (f : (t) -> u), ((@SAWCoreScaffolding.EqP) (u) (((f) (x))) (((f) (y)))) :=
  (fun (t : Type) (x : t) (y : t) (eq : ((@SAWCoreScaffolding.EqP) (t) (x) (y))) (u : Type) (f : (t) -> u) => ((@SAWCoreScaffolding.EqP__rec) (t) (x) ((fun (y' : t) (eq' : ((@SAWCoreScaffolding.EqP) (t) (x) (y'))) => ((@SAWCoreScaffolding.EqP) (u) (((f) (x))) (((f) (y')))))) (((@SAWCoreScaffolding.ReflP) (u) (((f) (x))))) (y) (eq))).

Definition sym : forall (a : Type), forall (x : a), forall (y : a), (((@SAWCoreScaffolding.Eq) (a) (x) (y))) -> ((@SAWCoreScaffolding.Eq) (a) (y) (x)) :=
  (fun (a : Type) (x : a) (y : a) (eq : ((@SAWCoreScaffolding.Eq) (a) (x) (y))) => ((@SAWCoreScaffolding.Eq__rec) (a) (x) ((fun (y' : a) (eq' : ((@SAWCoreScaffolding.Eq) (a) (x) (y'))) => ((@SAWCoreScaffolding.Eq) (a) (y') (x)))) (((@SAWCoreScaffolding.Refl) (a) (x))) (y) (eq))).

Definition trans : forall (a : Type), forall (x : a), forall (y : a), forall (z : a), (((@SAWCoreScaffolding.Eq) (a) (x) (y))) -> (((@SAWCoreScaffolding.Eq) (a) (y) (z))) -> ((@SAWCoreScaffolding.Eq) (a) (x) (z)) :=
  (fun (a : Type) (x : a) (y : a) (z : a) (eq1 : ((@SAWCoreScaffolding.Eq) (a) (x) (y))) (eq2 : ((@SAWCoreScaffolding.Eq) (a) (y) (z))) => ((@SAWCoreScaffolding.Eq__rec) (a) (y) ((fun (y' : a) (eq' : ((@SAWCoreScaffolding.Eq) (a) (y) (y'))) => ((@SAWCoreScaffolding.Eq) (a) (x) (y')))) (eq1) (z) (eq2))).

Definition transP : forall (a : Type), forall (x : a), forall (y : a), forall (z : a), (((@SAWCoreScaffolding.EqP) (a) (x) (y))) -> (((@SAWCoreScaffolding.EqP) (a) (y) (z))) -> ((@SAWCoreScaffolding.EqP) (a) (x) (z)) :=
  (fun (a : Type) (x : a) (y : a) (z : a) (eq1 : ((@SAWCoreScaffolding.EqP) (a) (x) (y))) (eq2 : ((@SAWCoreScaffolding.EqP) (a) (y) (z))) => ((@SAWCoreScaffolding.EqP__rec) (a) (y) ((fun (y' : a) (eq' : ((@SAWCoreScaffolding.EqP) (a) (y) (y'))) => ((@SAWCoreScaffolding.EqP) (a) (x) (y')))) (eq1) (z) (eq2))).

Definition trans2 : forall (a : Type), forall (x : a), forall (y : a), forall (z : a), (((@SAWCoreScaffolding.Eq) (a) (x) (z))) -> (((@SAWCoreScaffolding.Eq) (a) (y) (z))) -> ((@SAWCoreScaffolding.Eq) (a) (x) (y)) :=
  (fun (a : Type) (x : a) (y : a) (z : a) (eq1 : ((@SAWCoreScaffolding.Eq) (a) (x) (z))) (eq2 : ((@SAWCoreScaffolding.Eq) (a) (y) (z))) => ((@trans) (a) (x) (z) (y) (eq1) (((@sym) (a) (y) (z) (eq2))))).

Definition trans4 : forall (a : Type), forall (w : a), forall (x : a), forall (y : a), forall (z : a), (((@SAWCoreScaffolding.Eq) (a) (w) (x))) -> (((@SAWCoreScaffolding.Eq) (a) (x) (y))) -> (((@SAWCoreScaffolding.Eq) (a) (y) (z))) -> ((@SAWCoreScaffolding.Eq) (a) (w) (z)) :=
  (fun (a : Type) (w : a) (x : a) (y : a) (z : a) (eq1 : ((@SAWCoreScaffolding.Eq) (a) (w) (x))) (eq2 : ((@SAWCoreScaffolding.Eq) (a) (x) (y))) (eq3 : ((@SAWCoreScaffolding.Eq) (a) (y) (z))) => ((@trans) (a) (w) (x) (z) (eq1) (((@trans) (a) (x) (y) (z) (eq2) (eq3))))).

Definition eq_inv_map : forall (a : Type), forall (b : Type), forall (a1 : a), forall (a2 : a), (((@SAWCoreScaffolding.Eq) (a) (a1) (a2))) -> forall (f1 : (a) -> b), forall (f2 : (a) -> b), (((@SAWCoreScaffolding.Eq) (b) (((f1) (a2))) (((f2) (a2))))) -> ((@SAWCoreScaffolding.Eq) (b) (((f1) (a1))) (((f2) (a1)))) :=
  (fun (a : Type) (b : Type) (a1 : a) (a2 : a) (eq_a : ((@SAWCoreScaffolding.Eq) (a) (a1) (a2))) (f1 : (a) -> b) (f2 : (a) -> b) (eq_f : ((@SAWCoreScaffolding.Eq) (b) (((f1) (a2))) (((f2) (a2))))) => ((@trans) (b) (((f1) (a1))) (((f1) (a2))) (((f2) (a1))) (((@eq_cong) (a) (a1) (a2) (eq_a) (b) (f1))) (((@trans) (b) (((f1) (a2))) (((f2) (a2))) (((f2) (a1))) (eq_f) (((@eq_cong) (a) (a2) (a1) (((@sym) (a) (a1) (a2) (eq_a))) (b) (f2))))))).

(* Prelude.unsafeAssert was skipped *)

(* Prelude.coerce was skipped *)

(* Prelude.coerce__def was skipped *)

(* Prelude.coerce__eq was skipped *)

Definition coerceP : forall (a : Type), forall (b : Type), (((@SAWCoreScaffolding.EqP) (Type) (a) (b))) -> (a) -> b :=
  (fun (a : Type) (b : Type) (eq : ((@SAWCoreScaffolding.EqP) (Type) (a) (b))) (x : a) => ((@SAWCoreScaffolding.EqP__rec) (Type) (a) ((fun (b' : Type) (eq' : ((@SAWCoreScaffolding.EqP) (Type) (a) (b'))) => b')) (x) (b) (eq))).

(* Prelude.rcoerce was skipped *)

(* Prelude.unsafeCoerce was skipped *)

(* Prelude.unsafeCoerce_same was skipped *)

Definition piCong0 : forall (r : Type), forall (x : Type), forall (y : Type), (((@SAWCoreScaffolding.Eq) (Type) (x) (y))) -> ((@SAWCoreScaffolding.Eq) (Type) ((x) -> r) ((y) -> r)) :=
  (fun (r : Type) (x : Type) (y : Type) (eq : ((@SAWCoreScaffolding.Eq) (Type) (x) (y))) => ((@SAWCoreScaffolding.Eq__rec) (Type) (x) ((fun (y' : Type) (eq' : ((@SAWCoreScaffolding.Eq) (Type) (x) (y'))) => ((@SAWCoreScaffolding.Eq) (Type) ((x) -> r) ((y') -> r)))) (((@SAWCoreScaffolding.Refl) (Type) ((x) -> r))) (y) (eq))).

Definition piCong1 : forall (r : Type), forall (x : Type), forall (y : Type), (((@SAWCoreScaffolding.Eq) (Type) (x) (y))) -> ((@SAWCoreScaffolding.Eq) (Type) ((r) -> x) ((r) -> y)) :=
  (fun (r : Type) (x : Type) (y : Type) (eq : ((@SAWCoreScaffolding.Eq) (Type) (x) (y))) => ((@SAWCoreScaffolding.Eq__rec) (Type) (x) ((fun (y' : Type) (eq' : ((@SAWCoreScaffolding.Eq) (Type) (x) (y'))) => ((@SAWCoreScaffolding.Eq) (Type) ((r) -> x) ((r) -> y')))) (((@SAWCoreScaffolding.Refl) (Type) ((r) -> x))) (y) (eq))).

Inductive Bit : Type :=
| Bit1 : ((@Bit))
| Bit0 : ((@Bit))
.

Definition Bit__rec : forall (p : (((@Bit))) -> Type), (((p) (((@Bit1))))) -> (((p) (((@Bit0))))) -> forall (b : ((@Bit))), ((p) (b)) :=
  (fun (p : (((@Bit))) -> Type) (f1 : ((p) (((@Bit1))))) (f2 : ((p) (((@Bit0))))) (b : ((@Bit))) => ((SAWCorePrelude.Bit_rect) (p) (f1) (f2) (b))).

(* Prelude.Bool was skipped *)

(* Prelude.True was skipped *)

(* Prelude.False was skipped *)

(* Prelude.iteDep was skipped *)

(* Prelude.iteDep_True was skipped *)

(* Prelude.iteDep_False was skipped *)

(* Prelude.ite was skipped *)

(* Prelude.ite_eq_iteDep was skipped *)

Definition ite_true : forall (a : Type), forall (x : a), forall (y : a), ((@SAWCoreScaffolding.Eq) (a) (if ((@SAWCoreScaffolding.true)) then x else y) (x)) :=
  (fun (a : Type) (x : a) (y : a) => ((@trans) (a) (if ((@SAWCoreScaffolding.true)) then x else y) (((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => a)) (((@SAWCoreScaffolding.true))) (x) (y))) (x) (((@SAWCoreScaffolding.ite_eq_iteDep) (a) (((@SAWCoreScaffolding.true))) (x) (y))) (((@SAWCoreScaffolding.iteDep_True) ((fun (_ : ((@SAWCoreScaffolding.Bool))) => a)) (x) (y))))).

Definition ite_false : forall (a : Type), forall (x : a), forall (y : a), ((@SAWCoreScaffolding.Eq) (a) (if ((@SAWCoreScaffolding.false)) then x else y) (y)) :=
  (fun (a : Type) (x : a) (y : a) => ((@trans) (a) (if ((@SAWCoreScaffolding.false)) then x else y) (((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => a)) (((@SAWCoreScaffolding.false))) (x) (y))) (y) (((@SAWCoreScaffolding.ite_eq_iteDep) (a) (((@SAWCoreScaffolding.false))) (x) (y))) (((@SAWCoreScaffolding.iteDep_False) ((fun (_ : ((@SAWCoreScaffolding.Bool))) => a)) (x) (y))))).

Definition bool2bit : (((@SAWCoreScaffolding.Bool))) -> ((@Bit)) :=
  (fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (_ : ((@SAWCoreScaffolding.Bool))) => ((@Bit)))) (b) (((@Bit1))) (((@Bit0))))).

Definition bool2bit_True : ((@SAWCoreScaffolding.Eq) (((@Bit))) (((@bool2bit) (((@SAWCoreScaffolding.true))))) (((@Bit1)))) :=
  ((@SAWCoreScaffolding.iteDep_True) ((fun (_ : ((@SAWCoreScaffolding.Bool))) => ((@Bit)))) (((@Bit1))) (((@Bit0)))).

Definition bool2bit_False : ((@SAWCoreScaffolding.Eq) (((@Bit))) (((@bool2bit) (((@SAWCoreScaffolding.false))))) (((@Bit0)))) :=
  ((@SAWCoreScaffolding.iteDep_False) ((fun (_ : ((@SAWCoreScaffolding.Bool))) => ((@Bit)))) (((@Bit1))) (((@Bit0)))).

Definition bit2bool : (((@Bit))) -> ((@SAWCoreScaffolding.Bool)) :=
  ((@Bit__rec) ((fun (_ : ((@Bit))) => ((@SAWCoreScaffolding.Bool)))) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.false)))).

Definition bit2bool_Bit1 : ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@bit2bool) (((@Bit1))))) (((@SAWCoreScaffolding.true)))) :=
  ((@SAWCoreScaffolding.Refl) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.true)))).

Definition bit2bool_Bit0 : ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@bit2bool) (((@Bit0))))) (((@SAWCoreScaffolding.false)))) :=
  ((@SAWCoreScaffolding.Refl) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false)))).

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

Definition implies : (((@SAWCoreScaffolding.Bool))) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (a : ((@SAWCoreScaffolding.Bool))) (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (a))) (b))).

Definition implies__eq : forall (a : ((@SAWCoreScaffolding.Bool))), forall (b : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@implies) (a) (b))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (a))) (b)))) :=
  (fun (a : ((@SAWCoreScaffolding.Bool))) (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Refl) (((@SAWCoreScaffolding.Bool))) (((@implies) (a) (b))))).

Definition not_True : ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false)))) :=
  ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (if ((@SAWCoreScaffolding.true)) then ((@SAWCoreScaffolding.false)) else ((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.not__eq) (((@SAWCoreScaffolding.true))))) (((@ite_true) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.true)))))).

Definition not_False : ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true)))) :=
  ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (if ((@SAWCoreScaffolding.false)) then ((@SAWCoreScaffolding.false)) else ((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.not__eq) (((@SAWCoreScaffolding.false))))) (((@ite_false) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.true)))))).

Definition not_not : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.not) (x))))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.not) (b))))) (b)))) (x) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@not_True))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not))))) (((@not_False))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@not_False))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not))))) (((@not_True))))))).

Definition and_True1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.true))) (x))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.true))) (x))) (if ((@SAWCoreScaffolding.true)) then x else ((@SAWCoreScaffolding.false))) (x) (((@SAWCoreScaffolding.and__eq) (((@SAWCoreScaffolding.true))) (x))) (((@ite_true) (((@SAWCoreScaffolding.Bool))) (x) (((@SAWCoreScaffolding.false))))))).

Definition and_False1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.false))) (x))) (((@SAWCoreScaffolding.false)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.false))) (x))) (if ((@SAWCoreScaffolding.false)) then x else ((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.and__eq) (((@SAWCoreScaffolding.false))) (x))) (((@ite_false) (((@SAWCoreScaffolding.Bool))) (x) (((@SAWCoreScaffolding.false))))))).

Definition and_True2 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.true))))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (b) (((@SAWCoreScaffolding.true))))) (b)))) (x) (((@and_True1) (((@SAWCoreScaffolding.true))))) (((@and_False1) (((@SAWCoreScaffolding.true))))))).

Definition and_False2 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.false)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (b) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.false)))))) (x) (((@and_True1) (((@SAWCoreScaffolding.false))))) (((@and_False1) (((@SAWCoreScaffolding.false))))))).

Definition and_assoc : forall (x : ((@SAWCoreScaffolding.Bool))), forall (y : ((@SAWCoreScaffolding.Bool))), forall (z : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.and) (y) (z))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.and) (x) (y))) (z)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreScaffolding.Bool))) (z : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.and) (y) (b))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.and) (x) (y))) (b)))))) (z) (((@trans2) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.and) (y) (((@SAWCoreScaffolding.true))))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.and) (x) (y))) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.and) (x) (y))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (y) (((@SAWCoreScaffolding.true))))) (y) (((@and_True2) (y))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x))))) (((@and_True2) (((@SAWCoreScaffolding.and) (x) (y))))))) (((@trans2) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.and) (y) (((@SAWCoreScaffolding.false))))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.and) (x) (y))) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.false))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.and) (y) (((@SAWCoreScaffolding.false))))))) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.false))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (y) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.false))) (((@and_False2) (y))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x))))) (((@and_False2) (x))))) (((@and_False2) (((@SAWCoreScaffolding.and) (x) (y))))))))).

Definition and_idem : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x) (x))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (b) (b))) (b)))) (x) (((@and_True1) (((@SAWCoreScaffolding.true))))) (((@and_False1) (((@SAWCoreScaffolding.false))))))).

Definition or_True1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.true))) (x))) (((@SAWCoreScaffolding.true)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.true))) (x))) (if ((@SAWCoreScaffolding.true)) then ((@SAWCoreScaffolding.true)) else x) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.or__eq) (((@SAWCoreScaffolding.true))) (x))) (((@ite_true) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.true))) (x))))).

Definition or_False1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.false))) (x))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.false))) (x))) (if ((@SAWCoreScaffolding.false)) then ((@SAWCoreScaffolding.true)) else x) (x) (((@SAWCoreScaffolding.or__eq) (((@SAWCoreScaffolding.false))) (x))) (((@ite_false) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.true))) (x))))).

Definition or_True2 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.true)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (b) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.true)))))) (x) (((@or_True1) (((@SAWCoreScaffolding.true))))) (((@or_False1) (((@SAWCoreScaffolding.true))))))).

Definition or_False2 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.false))))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (b) (((@SAWCoreScaffolding.false))))) (b)))) (x) (((@or_True1) (((@SAWCoreScaffolding.false))))) (((@or_False1) (((@SAWCoreScaffolding.false))))))).

Definition or_assoc : forall (x : ((@SAWCoreScaffolding.Bool))), forall (y : ((@SAWCoreScaffolding.Bool))), forall (z : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.or) (y) (z))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.or) (x) (y))) (z)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreScaffolding.Bool))) (z : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.or) (y) (b))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.or) (x) (y))) (b)))))) (z) (((@trans2) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.or) (y) (((@SAWCoreScaffolding.true))))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.or) (x) (y))) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.true))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.or) (y) (((@SAWCoreScaffolding.true))))))) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.true))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (y) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.true))) (((@or_True2) (y))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (x))))) (((@or_True2) (x))))) (((@or_True2) (((@SAWCoreScaffolding.or) (x) (y))))))) (((@trans2) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.or) (y) (((@SAWCoreScaffolding.false))))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.or) (x) (y))) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.or) (x) (y))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (y) (((@SAWCoreScaffolding.false))))) (y) (((@or_False2) (y))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (x))))) (((@or_False2) (((@SAWCoreScaffolding.or) (x) (y))))))))).

Definition or_idem : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (x) (x))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (b) (b))) (b)))) (x) (((@or_True1) (((@SAWCoreScaffolding.true))))) (((@or_False1) (((@SAWCoreScaffolding.false))))))).

Definition implies_True1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@implies) (((@SAWCoreScaffolding.true))) (x))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (x))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.false))) (x))) (x) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@not_True))) (((@SAWCoreScaffolding.Bool))) ((fun (y : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.or) (y) (x)))))) (((@or_False1) (x))))).

Definition implies_False1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@implies) (((@SAWCoreScaffolding.false))) (x))) (((@SAWCoreScaffolding.true)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (x))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.true))) (x))) (((@SAWCoreScaffolding.true))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@not_False))) (((@SAWCoreScaffolding.Bool))) ((fun (y : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.or) (y) (x)))))) (((@or_True1) (x))))).

Definition true_implies : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@implies) (((@SAWCoreScaffolding.true))) (x))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@implies_True1) (x))).

Definition xor_True1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (((@SAWCoreScaffolding.true))) (x))) (((@SAWCoreScaffolding.not) (x)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (((@SAWCoreScaffolding.true))) (x))) (if ((@SAWCoreScaffolding.true)) then ((@SAWCoreScaffolding.not) (x)) else x) (((@SAWCoreScaffolding.not) (x))) (((@SAWCoreScaffolding.xor__eq) (((@SAWCoreScaffolding.true))) (x))) (((@ite_true) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (x))) (x))))).

Definition xor_False1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (((@SAWCoreScaffolding.false))) (x))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (((@SAWCoreScaffolding.false))) (x))) (if ((@SAWCoreScaffolding.false)) then ((@SAWCoreScaffolding.not) (x)) else x) (x) (((@SAWCoreScaffolding.xor__eq) (((@SAWCoreScaffolding.false))) (x))) (((@ite_false) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (x))) (x))))).

Definition xor_False2 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (x) (((@SAWCoreScaffolding.false))))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (b) (((@SAWCoreScaffolding.false))))) (b)))) (x) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@xor_True1) (((@SAWCoreScaffolding.false))))) (((@not_False))))) (((@xor_False1) (((@SAWCoreScaffolding.false))))))).

Definition xor_True2 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (x) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.not) (x)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (b) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.not) (b)))))) (x) (((@xor_True1) (((@SAWCoreScaffolding.true))))) (((@trans2) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@xor_False1) (((@SAWCoreScaffolding.true))))) (((@not_False))))))).

Definition xor_same : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (x) (x))) (((@SAWCoreScaffolding.false)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (b) (b))) (((@SAWCoreScaffolding.false)))))) (x) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.xor) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@xor_True1) (((@SAWCoreScaffolding.true))))) (((@not_True))))) (((@xor_False1) (((@SAWCoreScaffolding.false))))))).

Definition boolEq_True1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (((@SAWCoreScaffolding.true))) (x))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (((@SAWCoreScaffolding.true))) (x))) (if ((@SAWCoreScaffolding.true)) then x else ((@SAWCoreScaffolding.not) (x))) (x) (((@SAWCoreScaffolding.boolEq__eq) (((@SAWCoreScaffolding.true))) (x))) (((@ite_true) (((@SAWCoreScaffolding.Bool))) (x) (((@SAWCoreScaffolding.not) (x))))))).

Definition boolEq_False1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (((@SAWCoreScaffolding.false))) (x))) (((@SAWCoreScaffolding.not) (x)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (((@SAWCoreScaffolding.false))) (x))) (if ((@SAWCoreScaffolding.false)) then x else ((@SAWCoreScaffolding.not) (x))) (((@SAWCoreScaffolding.not) (x))) (((@SAWCoreScaffolding.boolEq__eq) (((@SAWCoreScaffolding.false))) (x))) (((@ite_false) (((@SAWCoreScaffolding.Bool))) (x) (((@SAWCoreScaffolding.not) (x))))))).

Definition boolEq_True2 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (x) (((@SAWCoreScaffolding.true))))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (b) (((@SAWCoreScaffolding.true))))) (b)))) (x) (((@boolEq_True1) (((@SAWCoreScaffolding.true))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@boolEq_False1) (((@SAWCoreScaffolding.true))))) (((@not_True))))))).

Definition boolEq_False2 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (x) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.not) (x)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (b) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.not) (b)))))) (x) (((@trans2) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@boolEq_True1) (((@SAWCoreScaffolding.false))))) (((@not_True))))) (((@boolEq_False1) (((@SAWCoreScaffolding.false))))))).

Definition boolEq_same : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (x) (x))) (((@SAWCoreScaffolding.true)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (b) (b))) (((@SAWCoreScaffolding.true)))))) (x) (((@boolEq_True1) (((@SAWCoreScaffolding.true))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@boolEq_False1) (((@SAWCoreScaffolding.false))))) (((@not_False))))))).

Definition not_or : forall (x : ((@SAWCoreScaffolding.Bool))), forall (y : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.or) (x) (y))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (x))) (((@SAWCoreScaffolding.not) (y)))))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.or) (b) (y))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (b))) (((@SAWCoreScaffolding.not) (y)))))))) (x) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.true))) (y))))) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.not) (y))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.true))) (y))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.true))) (y))) (((@SAWCoreScaffolding.true))) (((@or_True1) (y))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not))))) (((@not_True))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.not) (y))))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.false))) (((@and_False1) (((@SAWCoreScaffolding.not) (y))))))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@not_True))))) (((@SAWCoreScaffolding.Bool))) ((fun (z : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.and) (z) (((@SAWCoreScaffolding.not) (y)))))))))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.false))) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.not) (y))))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.false))) (y))) (y) (((@or_False1) (y))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not))))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@not_False))) (((@SAWCoreScaffolding.Bool))) ((fun (z : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.and) (z) (((@SAWCoreScaffolding.not) (y)))))))) (((@and_True1) (((@SAWCoreScaffolding.not) (y))))))))))))).

Definition not_and : forall (x : ((@SAWCoreScaffolding.Bool))), forall (y : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.and) (x) (y))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (x))) (((@SAWCoreScaffolding.not) (y)))))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.and) (b) (y))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (b))) (((@SAWCoreScaffolding.not) (y)))))))) (x) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.true))) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.not) (y))))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.true))) (y))) (y) (((@and_True1) (y))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not))))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.not) (y))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@not_True))) (((@SAWCoreScaffolding.Bool))) ((fun (z : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.or) (z) (((@SAWCoreScaffolding.not) (y)))))))) (((@or_False1) (((@SAWCoreScaffolding.not) (y))))))))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.false))) (y))))) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.not) (y))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.false))) (y))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.false))) (y))) (((@SAWCoreScaffolding.false))) (((@and_False1) (y))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not))))) (((@not_False))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.not) (y))))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.not) (y))))) (((@SAWCoreScaffolding.true))) (((@or_True1) (((@SAWCoreScaffolding.not) (y))))))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@not_False))))) (((@SAWCoreScaffolding.Bool))) ((fun (z : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.or) (z) (((@SAWCoreScaffolding.not) (y)))))))))))))).

Definition ite_not : forall (a : Type), forall (b : ((@SAWCoreScaffolding.Bool))), forall (x : a), forall (y : a), ((@SAWCoreScaffolding.Eq) (a) (if ((@SAWCoreScaffolding.not) (b)) then x else y) (if b then y else x)) :=
  (fun (a : Type) (b : ((@SAWCoreScaffolding.Bool))) (x : a) (y : a) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (a) (if ((@SAWCoreScaffolding.not) (b')) then x else y) (if b' then y else x)))) (b) (((@trans) (a) (if ((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true)))) then x else y) (y) (if ((@SAWCoreScaffolding.true)) then y else x) (((@trans) (a) (if ((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true)))) then x else y) (if ((@SAWCoreScaffolding.false)) then x else y) (y) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@not_True))) (a) ((fun (z : ((@SAWCoreScaffolding.Bool))) => if z then x else y)))) (((@ite_false) (a) (x) (y))))) (((@sym) (a) (if ((@SAWCoreScaffolding.true)) then y else x) (y) (((@ite_true) (a) (y) (x))))))) (((@trans) (a) (if ((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false)))) then x else y) (x) (if ((@SAWCoreScaffolding.false)) then y else x) (((@trans) (a) (if ((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false)))) then x else y) (if ((@SAWCoreScaffolding.true)) then x else y) (x) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@not_False))) (a) ((fun (z : ((@SAWCoreScaffolding.Bool))) => if z then x else y)))) (((@ite_true) (a) (x) (y))))) (((@sym) (a) (if ((@SAWCoreScaffolding.false)) then y else x) (x) (((@ite_false) (a) (y) (x))))))))).

Definition ite_nest1 : forall (a : Type), forall (b : ((@SAWCoreScaffolding.Bool))), forall (x : a), forall (y : a), forall (z : a), ((@SAWCoreScaffolding.Eq) (a) (if b then if b then x else y else z) (if b then x else z)) :=
  (fun (a : Type) (b : ((@SAWCoreScaffolding.Bool))) (x : a) (y : a) (z : a) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (a) (if b' then if b' then x else y else z) (if b' then x else z)))) (b) (((@trans) (a) (if ((@SAWCoreScaffolding.true)) then if ((@SAWCoreScaffolding.true)) then x else y else z) (x) (if ((@SAWCoreScaffolding.true)) then x else z) (((@trans) (a) (if ((@SAWCoreScaffolding.true)) then if ((@SAWCoreScaffolding.true)) then x else y else z) (if ((@SAWCoreScaffolding.true)) then x else y) (x) (((@ite_true) (a) (if ((@SAWCoreScaffolding.true)) then x else y) (z))) (((@ite_true) (a) (x) (y))))) (((@sym) (a) (if ((@SAWCoreScaffolding.true)) then x else z) (x) (((@ite_true) (a) (x) (z))))))) (((@trans) (a) (if ((@SAWCoreScaffolding.false)) then if ((@SAWCoreScaffolding.false)) then x else y else z) (z) (if ((@SAWCoreScaffolding.false)) then x else z) (((@ite_false) (a) (if ((@SAWCoreScaffolding.false)) then x else y) (z))) (((@sym) (a) (if ((@SAWCoreScaffolding.false)) then x else z) (z) (((@ite_false) (a) (x) (z))))))))).

Definition ite_nest2 : forall (a : Type), forall (b : ((@SAWCoreScaffolding.Bool))), forall (x : a), forall (y : a), forall (z : a), ((@SAWCoreScaffolding.Eq) (a) (if b then x else if b then y else z) (if b then x else z)) :=
  (fun (a : Type) (b : ((@SAWCoreScaffolding.Bool))) (x : a) (y : a) (z : a) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (a) (if b' then x else if b' then y else z) (if b' then x else z)))) (b) (((@trans) (a) (if ((@SAWCoreScaffolding.true)) then x else if ((@SAWCoreScaffolding.true)) then y else z) (x) (if ((@SAWCoreScaffolding.true)) then x else z) (((@ite_true) (a) (x) (if ((@SAWCoreScaffolding.true)) then y else z))) (((@sym) (a) (if ((@SAWCoreScaffolding.true)) then x else z) (x) (((@ite_true) (a) (x) (z))))))) (((@trans) (a) (if ((@SAWCoreScaffolding.false)) then x else if ((@SAWCoreScaffolding.false)) then y else z) (z) (if ((@SAWCoreScaffolding.false)) then x else z) (((@trans) (a) (if ((@SAWCoreScaffolding.false)) then x else if ((@SAWCoreScaffolding.false)) then y else z) (if ((@SAWCoreScaffolding.false)) then y else z) (z) (((@ite_false) (a) (x) (if ((@SAWCoreScaffolding.false)) then y else z))) (((@ite_false) (a) (y) (z))))) (((@sym) (a) (if ((@SAWCoreScaffolding.false)) then x else z) (z) (((@ite_false) (a) (x) (z))))))))).

(* Prelude.ite_bit was skipped *)

Definition ite_bit_false_1 : forall (b : ((@SAWCoreScaffolding.Bool))), forall (c : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (if b then ((@SAWCoreScaffolding.false)) else c) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (b))) (c)))) :=
  (fun (b : ((@SAWCoreScaffolding.Bool))) (c : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (if b' then ((@SAWCoreScaffolding.false)) else c) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (b'))) (c)))))) (b) (((@trans) (((@SAWCoreScaffolding.Bool))) (if ((@SAWCoreScaffolding.true)) then ((@SAWCoreScaffolding.false)) else c) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (c))) (((@ite_true) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))) (c))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (c))) (((@SAWCoreScaffolding.false))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (c))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.false))) (c))) (((@SAWCoreScaffolding.false))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@not_True))) (((@SAWCoreScaffolding.Bool))) ((fun (z : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.and) (z) (c)))))) (((@and_False1) (c))))))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (if ((@SAWCoreScaffolding.false)) then ((@SAWCoreScaffolding.false)) else c) (c) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (c))) (((@ite_false) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))) (c))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (c))) (c) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (c))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.true))) (c))) (c) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@not_False))) (((@SAWCoreScaffolding.Bool))) ((fun (z : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.and) (z) (c)))))) (((@and_True1) (c))))))))))).

Definition ite_bit_true_1 : forall (b : ((@SAWCoreScaffolding.Bool))), forall (c : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (if b then ((@SAWCoreScaffolding.true)) else c) (((@SAWCoreScaffolding.or) (b) (c)))) :=
  (fun (b : ((@SAWCoreScaffolding.Bool))) (c : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (if b' then ((@SAWCoreScaffolding.true)) else c) (((@SAWCoreScaffolding.or) (b') (c)))))) (b) (((@trans) (((@SAWCoreScaffolding.Bool))) (if ((@SAWCoreScaffolding.true)) then ((@SAWCoreScaffolding.true)) else c) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.true))) (c))) (((@ite_true) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.true))) (c))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.true))) (c))) (((@SAWCoreScaffolding.true))) (((@or_True1) (c))))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (if ((@SAWCoreScaffolding.false)) then ((@SAWCoreScaffolding.true)) else c) (c) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.false))) (c))) (((@ite_false) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.true))) (c))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.false))) (c))) (c) (((@or_False1) (c))))))))).

Definition ite_fold_not : forall (b : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (if b then ((@SAWCoreScaffolding.false)) else ((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.not) (b)))) :=
  (fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (if b' then ((@SAWCoreScaffolding.false)) else ((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.not) (b')))))) (b) (((@trans) (((@SAWCoreScaffolding.Bool))) (if ((@SAWCoreScaffolding.true)) then ((@SAWCoreScaffolding.false)) else ((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@ite_true) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.true))))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@not_True))))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (if ((@SAWCoreScaffolding.false)) then ((@SAWCoreScaffolding.false)) else ((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@ite_false) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.true))))) (((@sym) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@not_False))))))))).

Definition ite_eq : forall (a : Type), forall (b : ((@SAWCoreScaffolding.Bool))), forall (x : a), ((@SAWCoreScaffolding.Eq) (a) (if b then x else x) (x)) :=
  (fun (a : Type) (b : ((@SAWCoreScaffolding.Bool))) (x : a) => ((@SAWCoreScaffolding.iteDep) ((fun (b' : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (a) (if b' then x else x) (x)))) (b) (((@ite_true) (a) (x) (x))) (((@ite_false) (a) (x) (x))))).

Definition or_triv1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (x) (((@SAWCoreScaffolding.not) (x))))) (((@SAWCoreScaffolding.true)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (b) (((@SAWCoreScaffolding.not) (b))))) (((@SAWCoreScaffolding.true)))))) (x) (((@or_True1) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@or_False1) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))))) (((@not_False))))))).

Definition or_triv2 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (x))) (x))) (((@SAWCoreScaffolding.true)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (b))) (b))) (((@SAWCoreScaffolding.true)))))) (x) (((@or_True2) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))))) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))) (((@SAWCoreScaffolding.true))) (((@or_False2) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))))) (((@not_False))))))).

Definition and_triv1 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.not) (x))))) (((@SAWCoreScaffolding.false)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (b) (((@SAWCoreScaffolding.not) (b))))) (((@SAWCoreScaffolding.false)))))) (x) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@and_True1) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))))) (((@not_True))))) (((@and_False1) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))))))).

Definition and_triv2 : forall (x : ((@SAWCoreScaffolding.Bool))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (x))) (x))) (((@SAWCoreScaffolding.false)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (b))) (b))) (((@SAWCoreScaffolding.false)))))) (x) (((@trans) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))) (((@SAWCoreScaffolding.false))) (((@and_True2) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.true))))))) (((@not_True))))) (((@and_False2) (((@SAWCoreScaffolding.not) (((@SAWCoreScaffolding.false))))))))).

Definition EqTrue : (((@SAWCoreScaffolding.Bool))) -> Type :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (x) (((@SAWCoreScaffolding.true))))).

Definition TrueI : ((@EqTrue) (((@SAWCoreScaffolding.true)))) :=
  ((@SAWCoreScaffolding.Refl) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.true)))).

Definition andI : forall (x : ((@SAWCoreScaffolding.Bool))), forall (y : ((@SAWCoreScaffolding.Bool))), (((@EqTrue) (x))) -> (((@EqTrue) (y))) -> ((@EqTrue) (((@SAWCoreScaffolding.and) (x) (y)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreScaffolding.Bool))) (p : ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (x) (((@SAWCoreScaffolding.true))))) (q : ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (y) (((@SAWCoreScaffolding.true))))) => ((@trans4) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x) (y))) (((@SAWCoreScaffolding.and) (x) (((@SAWCoreScaffolding.true))))) (x) (((@SAWCoreScaffolding.true))) (((@eq_cong) (((@SAWCoreScaffolding.Bool))) (y) (((@SAWCoreScaffolding.true))) (q) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.and) (x))))) (((@and_True2) (x))) (p))).

Definition impliesI : forall (x : ((@SAWCoreScaffolding.Bool))), forall (y : ((@SAWCoreScaffolding.Bool))), ((((@EqTrue) (x))) -> ((@EqTrue) (y))) -> ((@EqTrue) (((@implies) (x) (y)))) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.iteDep) ((fun (x : ((@SAWCoreScaffolding.Bool))) => ((((@EqTrue) (x))) -> ((@EqTrue) (y))) -> ((@EqTrue) (((@implies) (x) (y)))))) (x) ((fun (H : (((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.true))) (((@SAWCoreScaffolding.true))))) -> ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (y) (((@SAWCoreScaffolding.true))))) => ((@trans) (((@SAWCoreScaffolding.Bool))) (((@implies) (((@SAWCoreScaffolding.true))) (y))) (y) (((@SAWCoreScaffolding.true))) (((@implies_True1) (y))) (((H) (((@TrueI)))))))) ((fun (_ : (((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))) (((@SAWCoreScaffolding.true))))) -> ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Bool))) (y) (((@SAWCoreScaffolding.true))))) => ((@implies_False1) (y)))))).

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
  (fun (s : Type) (t : Type) (p : (((@Either) (s) (t))) -> Type) (f1 : forall (l : s), ((p) (((@Left) (s) (t) (l))))) (f2 : forall (r : t), ((p) (((@Right) (s) (t) (r))))) (e : ((@Either) (s) (t))) => ((SAWCorePrelude.Either_rect) (s) (t) (p) (f1) (f2) (e))).

Definition either : forall (a : Type), forall (b : Type), forall (c : Type), ((a) -> c) -> ((b) -> c) -> (((@Either) (a) (b))) -> c :=
  (fun (a : Type) (b : Type) (c : Type) (f : (a) -> c) (g : (b) -> c) (e : ((@Either) (a) (b))) => ((@Either__rec) (a) (b) ((fun (p : ((@Either) (a) (b))) => c)) (f) (g) (e))).

Definition eitherCong0 : forall (t : Type), forall (x : Type), forall (y : Type), (((@SAWCoreScaffolding.Eq) (Type) (x) (y))) -> ((@SAWCoreScaffolding.Eq) (Type) (((@Either) (x) (t))) (((@Either) (y) (t)))) :=
  (fun (t : Type) (x : Type) (y : Type) (eq : ((@SAWCoreScaffolding.Eq) (Type) (x) (y))) => ((@eq_cong) (Type) (x) (y) (eq) (Type) ((fun (y' : Type) => ((@Either) (y') (t)))))).

Definition eitherCong1 : forall (t : Type), forall (x : Type), forall (y : Type), (((@SAWCoreScaffolding.Eq) (Type) (x) (y))) -> ((@SAWCoreScaffolding.Eq) (Type) (((@Either) (t) (x))) (((@Either) (t) (y)))) :=
  (fun (t : Type) (x : Type) (y : Type) (eq : ((@SAWCoreScaffolding.Eq) (Type) (x) (y))) => ((@eq_cong) (Type) (x) (y) (eq) (Type) ((fun (y' : Type) => ((@Either) (t) (y')))))).

Inductive Maybe (a : Type) : Type :=
| Nothing :  ((@Maybe) (a))
| Just : (a) -> ((@Maybe) (a))
.

Definition Maybe__rec : forall (a : Type), forall (p : (((@Maybe) (a))) -> Type), (((p) (((@Nothing) (a))))) -> (forall (x : a), ((p) (((@Just) (a) (x))))) -> forall (m : ((@Maybe) (a))), ((p) (m)) :=
  (fun (a : Type) (p : (((@Maybe) (a))) -> Type) (f1 : ((p) (((@Nothing) (a))))) (f2 : forall (x : a), ((p) (((@Just) (a) (x))))) (m : ((@Maybe) (a))) => ((SAWCorePrelude.Maybe_rect) (a) (p) (f1) (f2) (m))).

Definition maybe : forall (a : Type), forall (b : Type), (b) -> ((a) -> b) -> (((@Maybe) (a))) -> b :=
  (fun (a : Type) (b : Type) (f1 : b) (f2 : (a) -> b) (m : ((@Maybe) (a))) => ((@Maybe__rec) (a) ((fun (m' : ((@Maybe) (a))) => b)) (f1) (f2) (m))).

(* Prelude.Nat was skipped *)

Definition Nat__rec : forall (p : (((@SAWCoreScaffolding.Nat))) -> Type), (((p) (((@SAWCoreScaffolding.Zero))))) -> (forall (n : ((@SAWCoreScaffolding.Nat))), (((p) (n))) -> ((p) (((@SAWCoreScaffolding.Succ) (n))))) -> forall (n : ((@SAWCoreScaffolding.Nat))), ((p) (n)) :=
  (fun (p : (((@SAWCoreScaffolding.Nat))) -> Type) (f1 : ((p) (0))) (f2 : forall (n : ((@SAWCoreScaffolding.Nat))), (((p) (n))) -> ((p) (((@SAWCoreScaffolding.Succ) (n))))) (n : ((@SAWCoreScaffolding.Nat))) => ((SAWCoreScaffolding.Nat_rect) (p) (f1) (f2) (n))).

Definition Nat_cases : forall (a : Type), (a) -> ((((@SAWCoreScaffolding.Nat))) -> (a) -> a) -> (((@SAWCoreScaffolding.Nat))) -> a :=
  (fun (a : Type) (f1 : a) (f2 : (((@SAWCoreScaffolding.Nat))) -> (a) -> a) (n : ((@SAWCoreScaffolding.Nat))) => ((@Nat__rec) ((fun (n : ((@SAWCoreScaffolding.Nat))) => a)) (f1) (f2) (n))).

Definition Nat_cases2 : forall (a : Type), ((((@SAWCoreScaffolding.Nat))) -> a) -> ((((@SAWCoreScaffolding.Nat))) -> a) -> ((((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> (a) -> a) -> (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> a :=
  (fun (a : Type) (f1 : (((@SAWCoreScaffolding.Nat))) -> a) (f2 : (((@SAWCoreScaffolding.Nat))) -> a) (f3 : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> (a) -> a) (n : ((@SAWCoreScaffolding.Nat))) (m : ((@SAWCoreScaffolding.Nat))) => ((@Nat__rec) ((fun (n : ((@SAWCoreScaffolding.Nat))) => (((@SAWCoreScaffolding.Nat))) -> a)) (f1) ((fun (n : ((@SAWCoreScaffolding.Nat))) (f_rec : (((@SAWCoreScaffolding.Nat))) -> a) (m : ((@SAWCoreScaffolding.Nat))) => ((@Nat__rec) ((fun (m' : ((@SAWCoreScaffolding.Nat))) => a)) (((f2) (n))) ((fun (m' : ((@SAWCoreScaffolding.Nat))) (frec' : a) => ((f3) (n) (m') (((f_rec) (m')))))) (m)))) (n) (m))).

Definition eqNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> Type :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Nat))) (x) (y))).

Definition eqNatSucc : forall (x : ((@SAWCoreScaffolding.Nat))), forall (y : ((@SAWCoreScaffolding.Nat))), (((@eqNat) (x) (y))) -> ((@eqNat) (((@SAWCoreScaffolding.Succ) (x))) (((@SAWCoreScaffolding.Succ) (y)))) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) (eq : ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Nat))) (x) (y))) => ((@eq_cong) (((@SAWCoreScaffolding.Nat))) (x) (y) (eq) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (n)))))).

Definition pred : (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases) (((@SAWCoreScaffolding.Nat))) (((@SAWCoreScaffolding.Zero))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (m : ((@SAWCoreScaffolding.Nat))) => n)) (x))).

Definition eqNatPrec : forall (x : ((@SAWCoreScaffolding.Nat))), forall (y : ((@SAWCoreScaffolding.Nat))), (((@eqNat) (((@SAWCoreScaffolding.Succ) (x))) (((@SAWCoreScaffolding.Succ) (y))))) -> ((@eqNat) (x) (y)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) (eq' : ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Nat))) (((@SAWCoreScaffolding.Succ) (x))) (((@SAWCoreScaffolding.Succ) (y))))) => ((@eq_cong) (((@SAWCoreScaffolding.Nat))) (((@SAWCoreScaffolding.Succ) (x))) (((@SAWCoreScaffolding.Succ) (y))) (eq') (((@SAWCoreScaffolding.Nat))) (((@pred))))).

Inductive IsLeNat (n : ((@SAWCoreScaffolding.Nat))) : forall (_ : ((@SAWCoreScaffolding.Nat))), Prop :=
| IsLeNat_base :  ((@IsLeNat) (n) (n))
| IsLeNat_succ : forall (m : ((@SAWCoreScaffolding.Nat))), (((@IsLeNat) (n) (m))) -> ((@IsLeNat) (n) (((@SAWCoreScaffolding.Succ) (m))))
.

Definition IsLtNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> Prop :=
  (fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) => ((@IsLeNat) (((@SAWCoreScaffolding.Succ) (m))) (n))).

Axiom natCompareLe : forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), ((@Either) (((@IsLtNat) (m) (n))) (((@IsLeNat) (n) (m)))) .

Axiom proveEqNat : forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), ((@Maybe) (((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Nat))) (m) (n)))) .

Axiom proveLeNat : forall (x : ((@SAWCoreScaffolding.Nat))), forall (y : ((@SAWCoreScaffolding.Nat))), ((@Maybe) (((@IsLeNat) (x) (y)))) .

Definition proveLtNat : forall (x : ((@SAWCoreScaffolding.Nat))), forall (y : ((@SAWCoreScaffolding.Nat))), ((@Maybe) (((@IsLtNat) (x) (y)))) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@proveLeNat) (((@SAWCoreScaffolding.Succ) (x))) (y))).

Definition addNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases) (((@SAWCoreScaffolding.Nat))) (y) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (prev_sum : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (prev_sum)))) (x))).

Definition eqNatAdd0 : forall (x : ((@SAWCoreScaffolding.Nat))), ((@eqNat) (((@addNat) (x) (0))) (x)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) => ((@Nat__rec) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@eqNat) (((@addNat) (n) (0))) (n)))) (((@SAWCoreScaffolding.Refl) (((@SAWCoreScaffolding.Nat))) (0))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@eqNatSucc) (((@addNat) (n) (0))) (n)))) (x))).

Definition eqNatAddS : forall (x : ((@SAWCoreScaffolding.Nat))), forall (y : ((@SAWCoreScaffolding.Nat))), ((@eqNat) (((@addNat) (x) (((@SAWCoreScaffolding.Succ) (y))))) (((@SAWCoreScaffolding.Succ) (((@addNat) (x) (y)))))) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@Nat__rec) ((fun (x' : ((@SAWCoreScaffolding.Nat))) => forall (y' : ((@SAWCoreScaffolding.Nat))), ((@eqNat) (((@addNat) (x') (((@SAWCoreScaffolding.Succ) (y'))))) (((@SAWCoreScaffolding.Succ) (((@addNat) (x') (y')))))))) ((fun (y' : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Refl) (((@SAWCoreScaffolding.Nat))) (((@SAWCoreScaffolding.Succ) (y')))))) ((fun (x' : ((@SAWCoreScaffolding.Nat))) (eqF : forall (y' : ((@SAWCoreScaffolding.Nat))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Nat))) (((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Nat)))) (((@SAWCoreScaffolding.Succ) (y'))) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (prev_sum : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (prev_sum)))) (x'))) (((@SAWCoreScaffolding.Succ) (((@addNat) (x') (y'))))))) (y' : ((@SAWCoreScaffolding.Nat))) => ((@eqNatSucc) (((@addNat) (x') (((@SAWCoreScaffolding.Succ) (y'))))) (((@SAWCoreScaffolding.Succ) (((@addNat) (x') (y'))))) (((eqF) (y')))))) (x) (y))).

Definition eqNatAddComm : forall (x : ((@SAWCoreScaffolding.Nat))), forall (y : ((@SAWCoreScaffolding.Nat))), ((@eqNat) (((@addNat) (x) (y))) (((@addNat) (y) (x)))) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@Nat__rec) ((fun (y' : ((@SAWCoreScaffolding.Nat))) => forall (x' : ((@SAWCoreScaffolding.Nat))), ((@eqNat) (((@addNat) (x') (y'))) (((@addNat) (y') (x')))))) ((fun (x' : ((@SAWCoreScaffolding.Nat))) => ((@eqNatAdd0) (x')))) ((fun (y' : ((@SAWCoreScaffolding.Nat))) (eqF : forall (x' : ((@SAWCoreScaffolding.Nat))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Nat))) (((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Nat)))) (y') ((fun (_ : ((@SAWCoreScaffolding.Nat))) (prev_sum : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (prev_sum)))) (x'))) (((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Nat)))) (x') ((fun (_ : ((@SAWCoreScaffolding.Nat))) (prev_sum : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (prev_sum)))) (y'))))) (x' : ((@SAWCoreScaffolding.Nat))) => ((@trans) (((@SAWCoreScaffolding.Nat))) (((@addNat) (x') (((@SAWCoreScaffolding.Succ) (y'))))) (((@SAWCoreScaffolding.Succ) (((@addNat) (x') (y'))))) (((@SAWCoreScaffolding.Succ) (((@addNat) (y') (x'))))) (((@eqNatAddS) (x') (y'))) (((@eqNatSucc) (((@addNat) (x') (y'))) (((@addNat) (y') (x'))) (((eqF) (x')))))))) (y) (x))).

Definition addNat_assoc : forall (x : ((@SAWCoreScaffolding.Nat))), forall (y : ((@SAWCoreScaffolding.Nat))), forall (z : ((@SAWCoreScaffolding.Nat))), ((@eqNat) (((@addNat) (x) (((@addNat) (y) (z))))) (((@addNat) (((@addNat) (x) (y))) (z)))) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) (z : ((@SAWCoreScaffolding.Nat))) => ((@Nat__rec) ((fun (x' : ((@SAWCoreScaffolding.Nat))) => ((@eqNat) (((@addNat) (x') (((@addNat) (y) (z))))) (((@addNat) (((@addNat) (x') (y))) (z)))))) (((@SAWCoreScaffolding.Refl) (((@SAWCoreScaffolding.Nat))) (((@addNat) (y) (z))))) ((fun (x' : ((@SAWCoreScaffolding.Nat))) (eq : ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Nat))) (((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Nat)))) (((@addNat) (y) (z))) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (prev_sum : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (prev_sum)))) (x'))) (((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Nat)))) (z) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (prev_sum : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (prev_sum)))) (((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Nat)))) (y) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (prev_sum : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (prev_sum)))) (x'))))))) => ((@eqNatSucc) (((@addNat) (x') (((@addNat) (y) (z))))) (((@addNat) (((@addNat) (x') (y))) (z))) (eq)))) (x))).

Definition mulNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@Nat__rec) ((fun (x' : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Nat)))) (0) ((fun (x' : ((@SAWCoreScaffolding.Nat))) (prod : ((@SAWCoreScaffolding.Nat))) => ((@addNat) (y) (prod)))) (x))).

Definition equal0Nat : (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.true))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (b : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.false)))) (n))).

Definition equalNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases) ((((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Bool))) (((@equal0Nat))) ((fun (n' : ((@SAWCoreScaffolding.Nat))) (eqN : (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Bool))) (m : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))) ((fun (m' : ((@SAWCoreScaffolding.Nat))) (b : ((@SAWCoreScaffolding.Bool))) => ((eqN) (m')))) (m)))) (x) (y))).

Definition ltNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases2) (((@SAWCoreScaffolding.Bool))) ((fun (x' : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.false)))) ((fun (y' : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.true)))) ((fun (y' : ((@SAWCoreScaffolding.Nat))) (x' : ((@SAWCoreScaffolding.Nat))) (lt_mn : ((@SAWCoreScaffolding.Bool))) => lt_mn)) (y) (x))).

Definition subNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases2) (((@SAWCoreScaffolding.Nat))) ((fun (x' : ((@SAWCoreScaffolding.Nat))) => x')) ((fun (y' : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Zero)))) ((fun (y' : ((@SAWCoreScaffolding.Nat))) (x' : ((@SAWCoreScaffolding.Nat))) (sub_xy : ((@SAWCoreScaffolding.Nat))) => sub_xy)) (y) (x))).

Definition minNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases2) (((@SAWCoreScaffolding.Nat))) ((fun (y' : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Zero)))) ((fun (x' : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Zero)))) ((fun (x' : ((@SAWCoreScaffolding.Nat))) (y' : ((@SAWCoreScaffolding.Nat))) (min_xy : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (min_xy)))) (x) (y))).

Definition maxNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases2) (((@SAWCoreScaffolding.Nat))) ((fun (x' : ((@SAWCoreScaffolding.Nat))) => x')) ((fun (y' : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (y')))) ((fun (y' : ((@SAWCoreScaffolding.Nat))) (x' : ((@SAWCoreScaffolding.Nat))) (sub_xy : ((@SAWCoreScaffolding.Nat))) => sub_xy)) (y) (x))).

(* Prelude.widthNat was skipped *)

(* Prelude.eq_Nat was skipped *)

Definition expNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (b : ((@SAWCoreScaffolding.Nat))) (e : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases) (((@SAWCoreScaffolding.Nat))) (1) ((fun (e' : ((@SAWCoreScaffolding.Nat))) (exp_b_e : ((@SAWCoreScaffolding.Nat))) => ((@mulNat) (b) (exp_b_e)))) (e))).

(* Prelude.divModNat was skipped *)

Definition divNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((SAWCoreScaffolding.fst) (((@SAWCoreScaffolding.divModNat) (x) (y))))).

Definition modNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((SAWCoreScaffolding.snd) (((@SAWCoreScaffolding.divModNat) (x) (y))))).

Definition natCase : forall (p : (((@SAWCoreScaffolding.Nat))) -> Type), (((p) (((@SAWCoreScaffolding.Zero))))) -> (forall (n : ((@SAWCoreScaffolding.Nat))), ((p) (((@SAWCoreScaffolding.Succ) (n))))) -> forall (n : ((@SAWCoreScaffolding.Nat))), ((p) (n)) :=
  (fun (p : (((@SAWCoreScaffolding.Nat))) -> Type) (z : ((p) (0))) (s : forall (n : ((@SAWCoreScaffolding.Nat))), ((p) (((@SAWCoreScaffolding.Succ) (n))))) => ((@Nat__rec) (p) (z) ((fun (n : ((@SAWCoreScaffolding.Nat))) (r : ((p) (n))) => ((s) (n)))))).

Definition if0Nat : forall (a : Type), (((@SAWCoreScaffolding.Nat))) -> (a) -> (a) -> a :=
  (fun (a : Type) (n : ((@SAWCoreScaffolding.Nat))) (x : a) (y : a) => ((@natCase) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => a)) (x) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => y)) (n))).

(* Prelude.Vec was skipped *)

(* Prelude.gen was skipped *)

(* Prelude.atWithDefault was skipped *)

Definition sawAt : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCoreScaffolding.Nat))) -> a :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.atWithDefault) (n) (a) (((@SAWCoreScaffolding.error) (a) (("at: index out of bounds")%string))) (v) (i))).

(* Prelude.EmptyVec was skipped *)

Definition ConsVec : forall (a : Type), (a) -> forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n))) (a)) :=
  (fun (a : Type) (x : a) (n : ((@SAWCoreScaffolding.Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (((@SAWCoreScaffolding.Succ) (n))) (a) (((@Nat_cases) (a) (x) ((fun (i : ((@SAWCoreScaffolding.Nat))) (a' : a) => ((@SAWCorePrelude.sawAt) (n) (a) (v) (i)))))))).

Definition upd : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCoreScaffolding.Nat))) -> (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (j : ((@SAWCoreScaffolding.Nat))) (x : a) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => if ((@equalNat) (i) (j)) then x else ((@SAWCorePrelude.sawAt) (n) (a) (v) (i)))))).

Definition map : forall (a : Type), forall (b : Type), ((a) -> b) -> forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (b)) :=
  (fun (a : Type) (b : Type) (f : (a) -> b) (n : ((@SAWCoreScaffolding.Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (b) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((f) (((@SAWCorePrelude.sawAt) (n) (a) (v) (i)))))))).

Definition zipWith : forall (a : Type), forall (b : Type), forall (c : Type), ((a) -> (b) -> c) -> forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (b))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (c)) :=
  (fun (a : Type) (b : Type) (c : Type) (f : (a) -> (b) -> c) (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (b))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (c) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((f) (((@SAWCorePrelude.sawAt) (n) (a) (x) (i))) (((@SAWCorePrelude.sawAt) (n) (b) (y) (i)))))))).

Definition replicate : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (x : a) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => x)))).

Definition single : forall (a : Type), (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (1) (a)) :=
  ((@replicate) (1)).

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

Definition reverse : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.sawAt) (n) (a) (xs) (((@subNat) (((@subNat) (n) (1))) (i)))))))).

Definition transpose : forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a)))) :=
  (fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (xss : ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) ((fun (j : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.gen) (m) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.sawAt) (n) (a) (((@SAWCorePrelude.sawAt) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (xss) (i))) (j))))))))).

Definition vecEq : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (eqFn : (a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) => ((@SAWCoreVectorsAsCoqVectors.foldr) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Bool))) (n) (((@SAWCoreScaffolding.and))) (((@SAWCoreScaffolding.true))) (((@zipWith) (a) (a) (((@SAWCoreScaffolding.Bool))) (eqFn) (n) (x) (y))))).

(* Prelude.eq_Vec was skipped *)

Definition take : forall (a : Type), forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (((@addNat) (m) (n))) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a)) :=
  (fun (a : Type) (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@addNat) (m) (n))) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (m) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.sawAt) (((@addNat) (m) (n))) (a) (v) (i)))))).

Definition vecCong : forall (a : Type), forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Nat))) (m) (n))) -> ((@SAWCoreScaffolding.Eq) (Type) (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (a : Type) (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (eq : ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Nat))) (m) (n))) => ((@eq_cong) (((@SAWCoreScaffolding.Nat))) (m) (n) (eq) (Type) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.Vec) (i) (a)))))).

(* Prelude.coerceVec was skipped *)

(* Prelude.take0 was skipped *)

Definition drop : forall (a : Type), forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (((@addNat) (m) (n))) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (a : Type) (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@addNat) (m) (n))) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.sawAt) (((@addNat) (m) (n))) (a) (v) (((@addNat) (m) (i)))))))).

(* Prelude.drop0 was skipped *)

Definition slice : forall (a : Type), forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), forall (o : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (((@addNat) (((@addNat) (m) (n))) (o))) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (a : Type) (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (o : ((@SAWCoreScaffolding.Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@addNat) (((@addNat) (m) (n))) (o))) (a))) => ((@drop) (a) (m) (n) (((@take) (a) (((@addNat) (m) (n))) (o) (v))))).

Definition join : forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (((@mulNat) (m) (n))) (a)) :=
  (fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) => ((@SAWCoreVectorsAsCoqVectors.gen) (((@mulNat) (m) (n))) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.sawAt) (n) (a) (((@SAWCorePrelude.sawAt) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (v) (((@divNat) (i) (n))))) (((@modNat) (i) (n)))))))).

Definition split : forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (((@mulNat) (m) (n))) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@mulNat) (m) (n))) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (j : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.sawAt) (((@mulNat) (m) (n))) (a) (v) (((@addNat) (((@mulNat) (i) (n))) (j))))))))))).

Definition append : forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (((@addNat) (m) (n))) (a)) :=
  (fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (((@addNat) (m) (n))) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => if ((@ltNat) (i) (m)) then ((@SAWCorePrelude.sawAt) (m) (a) (x) (i)) else ((@SAWCorePrelude.sawAt) (n) (a) (y) (((@subNat) (i) (m)))))))).

(* Prelude.rotateL was skipped *)

(* Prelude.rotateR was skipped *)

(* Prelude.shiftL was skipped *)

(* Prelude.shiftR was skipped *)

Definition joinLittleEndian : forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (((@mulNat) (m) (n))) (a)) :=
  (fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) => ((@join) (m) (n) (a) (((@reverse) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (v))))).

Definition splitLittleEndian : forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (((@mulNat) (m) (n))) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@mulNat) (m) (n))) (a))) => ((@reverse) (m) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (((@split) (m) (n) (a) (v))))).

Definition bitvector : forall (n : ((@SAWCoreScaffolding.Nat))), Type :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))).

Definition msb : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (((@SAWCoreScaffolding.Succ) (n))))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n))) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCorePrelude.sawAt) (((@SAWCoreScaffolding.Succ) (n))) (((@SAWCoreScaffolding.Bool))) (v) (0))).

Definition lsb : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (((@SAWCoreScaffolding.Succ) (n))))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (v : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n))) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCorePrelude.sawAt) (((@SAWCoreScaffolding.Succ) (n))) (((@SAWCoreScaffolding.Bool))) (v) (n))).

(* Prelude.bvNat was skipped *)

(* Prelude.bvToNat was skipped *)

Definition bvAt : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), forall (w : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@bitvector) (w))) -> a :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (w : ((@SAWCoreScaffolding.Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCorePrelude.sawAt) (n) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

Definition bvUpd : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), forall (w : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@bitvector) (w))) -> (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (w : ((@SAWCoreScaffolding.Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (((@SAWCoreScaffolding.Bool))))) (y : a) => ((@upd) (n) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))) (y))).

Definition bvRotateL : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), forall (w : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@bitvector) (w))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (w : ((@SAWCoreScaffolding.Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreVectorsAsCoqVectors.rotateL) (n) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

Definition bvRotateR : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), forall (w : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@bitvector) (w))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (w : ((@SAWCoreScaffolding.Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreVectorsAsCoqVectors.rotateR) (n) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

Definition bvShiftL : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), forall (w : ((@SAWCoreScaffolding.Nat))), (a) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@bitvector) (w))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (w : ((@SAWCoreScaffolding.Nat))) (z : a) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreVectorsAsCoqVectors.shiftL) (n) (a) (z) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

Definition bvShiftR : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), forall (w : ((@SAWCoreScaffolding.Nat))), (a) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@bitvector) (w))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (w : ((@SAWCoreScaffolding.Nat))) (z : a) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreVectorsAsCoqVectors.shiftR) (n) (a) (z) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

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

Definition bvCarry : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> (((@bitvector) (n))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreVectorsAsCoqVectors.bvult) (n) (((@SAWCoreVectorsAsCoqVectors.bvAdd) (n) (x) (y))) (x))).

Definition bvSCarry : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (((@SAWCoreScaffolding.Succ) (n))))) -> (((@bitvector) (((@SAWCoreScaffolding.Succ) (n))))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n))) (((@SAWCoreScaffolding.Bool))))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n))) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.boolEq) (((@msb) (n) (x))) (((@msb) (n) (y))))) (((@SAWCoreScaffolding.xor) (((@msb) (n) (x))) (((@msb) (n) (((@SAWCoreVectorsAsCoqVectors.bvAdd) (((@SAWCoreScaffolding.Succ) (n))) (x) (y))))))))).

Definition bvAddWithCarry : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> (((@bitvector) (n))) -> ((prod) (((@SAWCoreScaffolding.Bool))) (((@bitvector) (n)))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) => ((pair) (((@bvCarry) (n) (x) (y))) (((@SAWCoreVectorsAsCoqVectors.bvAdd) (n) (x) (y))))).

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

Definition bvZipWith : ((((@SAWCoreScaffolding.Bool))) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) -> forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> (((@bitvector) (n))) -> ((@bitvector) (n)) :=
  ((@zipWith) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Bool)))).

Definition bvNot : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> ((@bitvector) (n)) :=
  ((@map) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.not)))).

Definition bvAnd : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> (((@bitvector) (n))) -> ((@bitvector) (n)) :=
  ((@bvZipWith) (((@SAWCoreScaffolding.and)))).

Definition bvOr : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> (((@bitvector) (n))) -> ((@bitvector) (n)) :=
  ((@bvZipWith) (((@SAWCoreScaffolding.or)))).

Definition bvXor : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> (((@bitvector) (n))) -> ((@bitvector) (n)) :=
  ((@bvZipWith) (((@SAWCoreScaffolding.xor)))).

Definition bvEq : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> (((@bitvector) (n))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) => ((@vecEq) (n) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.boolEq))) (x) (y))).

(* Prelude.bvEq_refl was skipped *)

(* Prelude.eq_bitvector was skipped *)

(* Prelude.eq_VecBool was skipped *)

(* Prelude.eq_VecVec was skipped *)

(* Prelude.equalNat_bv was skipped *)

Definition bvBool : forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreScaffolding.Bool))) -> ((@bitvector) (n)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (b : ((@SAWCoreScaffolding.Bool))) => if b then ((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (1)) else ((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (0))).

Definition bvNe : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> (((@bitvector) (n))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreScaffolding.not) (((@bvEq) (n) (x) (y))))).

Definition bvNonzero : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) => ((@bvNe) (n) (x) (((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (0))))).

Definition bvTrunc : forall (x : ((@SAWCoreScaffolding.Nat))), forall (y : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (((@addNat) (x) (y))))) -> ((@bitvector) (y)) :=
  ((@drop) (((@SAWCoreScaffolding.Bool)))).

Definition bvUExt : forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> ((@bitvector) (((@addNat) (m) (n)))) :=
  (fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) => ((@append) (m) (n) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvNat) (m) (0))) (x))).

Definition replicateBool : forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreScaffolding.Bool))) -> ((@bitvector) (n)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (b : ((@SAWCoreScaffolding.Bool))) => if b then ((@bvNot) (n) (((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (0)))) else ((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (0))).

Definition bvSExt : forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (((@SAWCoreScaffolding.Succ) (n))))) -> ((@bitvector) (((@addNat) (m) (((@SAWCoreScaffolding.Succ) (n)))))) :=
  (fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n))) (((@SAWCoreScaffolding.Bool))))) => ((@append) (m) (((@SAWCoreScaffolding.Succ) (n))) (((@SAWCoreScaffolding.Bool))) (((@replicateBool) (m) (((@msb) (n) (x))))) (x))).

Inductive Stream (a : Type) : Type :=
| MkStream : ((((@SAWCoreScaffolding.Nat))) -> a) -> ((@Stream) (a))
.

Definition Stream__rec : forall (a : Type), forall (p : (((@Stream) (a))) -> Type), (forall (f : (((@SAWCoreScaffolding.Nat))) -> a), ((p) (((@MkStream) (a) (f))))) -> forall (str : ((@Stream) (a))), ((p) (str)) :=
  (fun (a : Type) (p : (((@Stream) (a))) -> Type) (f1 : forall (f : (((@SAWCoreScaffolding.Nat))) -> a), ((p) (((@MkStream) (a) (f))))) (str : ((@Stream) (a))) => ((SAWCorePrelude.Stream_rect) (a) (p) (f1) (str))).

Definition streamUpd : forall (a : Type), (((@Stream) (a))) -> (((@SAWCoreScaffolding.Nat))) -> (a) -> ((@Stream) (a)) :=
  (fun (a : Type) (strm : ((@Stream) (a))) (i : ((@SAWCoreScaffolding.Nat))) (y : a) => ((@Stream__rec) (a) ((fun (strm' : ((@Stream) (a))) => ((@Stream) (a)))) ((fun (s : (((@SAWCoreScaffolding.Nat))) -> a) => ((@MkStream) (a) ((fun (j : ((@SAWCoreScaffolding.Nat))) => if ((@equalNat) (i) (j)) then y else ((s) (j))))))) (strm))).

Definition bvStreamUpd : forall (a : Type), forall (w : ((@SAWCoreScaffolding.Nat))), (((@Stream) (a))) -> (((@bitvector) (w))) -> (a) -> ((@Stream) (a)) :=
  (fun (a : Type) (w : ((@SAWCoreScaffolding.Nat))) (xs : ((@Stream) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (((@SAWCoreScaffolding.Bool))))) (y : a) => ((@streamUpd) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))) (y))).

Definition streamGet : forall (a : Type), (((@Stream) (a))) -> (((@SAWCoreScaffolding.Nat))) -> a :=
  (fun (a : Type) (strm : ((@Stream) (a))) (i : ((@SAWCoreScaffolding.Nat))) => ((@Stream__rec) (a) ((fun (strm' : ((@Stream) (a))) => a)) ((fun (s : (((@SAWCoreScaffolding.Nat))) -> a) => ((s) (i)))) (strm))).

Definition streamConst : forall (a : Type), (a) -> ((@Stream) (a)) :=
  (fun (a : Type) (x : a) => ((@MkStream) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => x)))).

Definition streamMap : forall (a : Type), forall (b : Type), ((a) -> b) -> (((@Stream) (a))) -> ((@Stream) (b)) :=
  (fun (a : Type) (b : Type) (f : (a) -> b) (xs : ((@Stream) (a))) => ((@MkStream) (b) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((f) (((@streamGet) (a) (xs) (i)))))))).

Definition streamMap2 : forall (a : Type), forall (b : Type), forall (c : Type), ((a) -> (b) -> c) -> (((@Stream) (a))) -> (((@Stream) (b))) -> ((@Stream) (c)) :=
  (fun (a : Type) (b : Type) (c : Type) (f : (a) -> (b) -> c) (xs : ((@Stream) (a))) (ys : ((@Stream) (b))) => ((@MkStream) (c) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((f) (((@streamGet) (a) (xs) (i))) (((@streamGet) (b) (ys) (i)))))))).

Definition streamTake : forall (a : Type), forall (n : ((@SAWCoreScaffolding.Nat))), (((@Stream) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) :=
  (fun (a : Type) (n : ((@SAWCoreScaffolding.Nat))) (xs : ((@Stream) (a))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@streamGet) (a) (xs) (i)))))).

Definition streamDrop : forall (a : Type), forall (n : ((@SAWCoreScaffolding.Nat))), (((@Stream) (a))) -> ((@Stream) (a)) :=
  (fun (a : Type) (n : ((@SAWCoreScaffolding.Nat))) (xs : ((@Stream) (a))) => ((@MkStream) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@streamGet) (a) (xs) (((@addNat) (n) (i)))))))).

Definition streamAppend : forall (a : Type), forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@Stream) (a))) -> ((@Stream) (a)) :=
  (fun (a : Type) (n : ((@SAWCoreScaffolding.Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (ys : ((@Stream) (a))) => ((@MkStream) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.atWithDefault) (n) (a) (((@streamGet) (a) (ys) (((@subNat) (i) (n))))) (xs) (i)))))).

Definition streamJoin : forall (a : Type), forall (n : ((@SAWCoreScaffolding.Nat))), (((@Stream) (((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n))) (a))))) -> ((@Stream) (a)) :=
  (fun (a : Type) (n : ((@SAWCoreScaffolding.Nat))) (s : ((@Stream) (((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n))) (a))))) => ((@MkStream) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.sawAt) (((@SAWCoreScaffolding.Succ) (n))) (a) (((@streamGet) (((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n))) (a))) (s) (((@divNat) (i) (((@SAWCoreScaffolding.Succ) (n))))))) (((@modNat) (i) (((@SAWCoreScaffolding.Succ) (n)))))))))).

Definition streamSplit : forall (a : Type), forall (n : ((@SAWCoreScaffolding.Nat))), (((@Stream) (a))) -> ((@Stream) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (a : Type) (n : ((@SAWCoreScaffolding.Nat))) (xs : ((@Stream) (a))) => ((@MkStream) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (a) ((fun (j : ((@SAWCoreScaffolding.Nat))) => ((@streamGet) (a) (xs) (((@addNat) (((@mulNat) (i) (n))) (j))))))))))).

Definition bvStreamGet : forall (a : Type), forall (w : ((@SAWCoreScaffolding.Nat))), (((@Stream) (a))) -> (((@bitvector) (w))) -> a :=
  (fun (a : Type) (w : ((@SAWCoreScaffolding.Nat))) (xs : ((@Stream) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (((@SAWCoreScaffolding.Bool))))) => ((@streamGet) (a) (xs) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))).

Definition bvStreamShiftL : forall (a : Type), forall (w : ((@SAWCoreScaffolding.Nat))), (((@Stream) (a))) -> (((@bitvector) (w))) -> ((@Stream) (a)) :=
  (fun (a : Type) (w : ((@SAWCoreScaffolding.Nat))) (xs : ((@Stream) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (((@SAWCoreScaffolding.Bool))))) => ((@streamDrop) (a) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))) (xs))).

Definition bvStreamShiftR : forall (a : Type), forall (w : ((@SAWCoreScaffolding.Nat))), (a) -> (((@Stream) (a))) -> (((@bitvector) (w))) -> ((@Stream) (a)) :=
  (fun (a : Type) (w : ((@SAWCoreScaffolding.Nat))) (x : a) (xs : ((@Stream) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (((@SAWCoreScaffolding.Bool))))) => ((@streamAppend) (a) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))) (((@replicate) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))) (a) (x))) (xs))).

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

Axiom intToBv : forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCoreScaffolding.Integer))) -> ((@bitvector) (n)) .

Axiom bvToInt : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> ((@SAWCoreScaffolding.Integer)) .

(* Prelude.sbvToInt was skipped *)

(* Prelude.IntMod was skipped *)

(* Prelude.toIntMod was skipped *)

(* Prelude.fromIntMod was skipped *)

(* Prelude.intModEq was skipped *)

(* Prelude.intModAdd was skipped *)

(* Prelude.intModSub was skipped *)

(* Prelude.intModMul was skipped *)

(* Prelude.intModNeg was skipped *)

Definition updNatFun : forall (a : Type), ((((@SAWCoreScaffolding.Nat))) -> a) -> (((@SAWCoreScaffolding.Nat))) -> (a) -> (((@SAWCoreScaffolding.Nat))) -> a :=
  (fun (a : Type) (f : (((@SAWCoreScaffolding.Nat))) -> a) (i : ((@SAWCoreScaffolding.Nat))) (v : a) (x : ((@SAWCoreScaffolding.Nat))) => if ((@equalNat) (i) (x)) then v else ((f) (x))).

Definition updBvFun : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), ((((@bitvector) (n))) -> a) -> (((@bitvector) (n))) -> (a) -> (((@bitvector) (n))) -> a :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (f : (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) -> a) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (v : a) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) => if ((@bvEq) (n) (i) (x)) then v else ((f) (x))).

(* Prelude.Float was skipped *)

(* Prelude.mkFloat was skipped *)

(* Prelude.Double was skipped *)

(* Prelude.mkDouble was skipped *)

Axiom bvEqWithProof : forall (n : ((@SAWCoreScaffolding.Nat))), forall (v1 : ((@bitvector) (n))), forall (v2 : ((@bitvector) (n))), ((@Maybe) (((@SAWCoreScaffolding.EqP) (((@bitvector) (n))) (v1) (v2)))) .

Axiom bvultWithProof : forall (n : ((@SAWCoreScaffolding.Nat))), forall (v1 : ((@bitvector) (n))), forall (v2 : ((@bitvector) (n))), ((@Maybe) (((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (n) (v1) (v2))) (((@SAWCoreScaffolding.true)))))) .

Axiom bvEqToEqNat : forall (n : ((@SAWCoreScaffolding.Nat))), forall (v1 : ((@bitvector) (n))), forall (v2 : ((@bitvector) (n))), (((@SAWCoreScaffolding.EqP) (((@bitvector) (n))) (v1) (v2))) -> ((@eqNat) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (n) (v1))) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (n) (v2)))) .

Axiom bvultToIsLtNat : forall (n : ((@SAWCoreScaffolding.Nat))), forall (v1 : ((@bitvector) (n))), forall (v2 : ((@bitvector) (n))), (((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (n) (v1) (v2))) (((@SAWCoreScaffolding.true))))) -> ((@IsLtNat) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (n) (v1))) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (n) (v2)))) .

Axiom atWithProof : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (a) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> forall (i : ((@SAWCoreScaffolding.Nat))), (((@IsLtNat) (i) (n))) -> a .

Axiom updWithProof : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> forall (i : ((@SAWCoreScaffolding.Nat))), (a) -> (((@IsLtNat) (i) (n))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) .

Axiom sliceWithProof : forall (a : Type), forall (n : ((@SAWCoreScaffolding.Nat))), forall (off : ((@SAWCoreScaffolding.Nat))), forall (len : ((@SAWCoreScaffolding.Nat))), (((@IsLeNat) (((@addNat) (off) (len))) (n))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (len) (a)) .

Axiom updSliceWithProof : forall (a : Type), forall (n : ((@SAWCoreScaffolding.Nat))), forall (off : ((@SAWCoreScaffolding.Nat))), forall (len : ((@SAWCoreScaffolding.Nat))), (((@IsLeNat) (((@addNat) (off) (len))) (n))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (len) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)) .

Axiom BVVec : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> (Type) -> Type .

Axiom genBVVec : forall (n : ((@SAWCoreScaffolding.Nat))), forall (len : ((@bitvector) (n))), forall (a : Type), ((((@bitvector) (n))) -> a) -> ((@BVVec) (n) (len) (a)) .

Axiom atBVVec : forall (n : ((@SAWCoreScaffolding.Nat))), forall (len : ((@bitvector) (n))), forall (a : Type), (((@BVVec) (n) (len) (a))) -> forall (ix : ((@bitvector) (n))), (((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (n) (ix) (len))) (((@SAWCoreScaffolding.true))))) -> a .

Axiom at_gen_BVVec : forall (n : ((@SAWCoreScaffolding.Nat))), forall (len : ((@bitvector) (n))), forall (a : Type), forall (f : (((@bitvector) (n))) -> a), forall (ix : ((@bitvector) (n))), forall (pf : ((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (n) (ix) (len))) (((@SAWCoreScaffolding.true))))), ((@SAWCoreScaffolding.EqP) (a) (((@atBVVec) (n) (len) (a) (((@genBVVec) (n) (len) (a) (f))) (ix) (pf))) (((f) (ix)))) .

Definition updBVVec : forall (n : ((@SAWCoreScaffolding.Nat))), forall (len : ((@bitvector) (n))), forall (a : Type), (((@BVVec) (n) (len) (a))) -> forall (ix : ((@bitvector) (n))), (((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (n) (ix) (len))) (((@SAWCoreScaffolding.true))))) -> (a) -> ((@BVVec) (n) (len) (a)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (a : Type) (v : ((@BVVec) (n) (len) (a))) (ix : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (pf : ((@SAWCoreScaffolding.EqP) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreVectorsAsCoqVectors.bvult) (n) (ix) (len))) (((@SAWCoreScaffolding.true))))) (elem : a) => ((@genBVVec) (n) (len) (a) ((fun (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) => if ((@bvEq) (n) (i) (ix)) then elem else ((@atBVVec) (n) (len) (a) (v) (ix) (pf)))))).

(* Prelude.Sigma was skipped *)

(* Prelude.Sigma__rec was skipped *)

Definition Sigma_proj1 : forall (a : Type), forall (b : (a) -> Type), (((@sigT) (a) (b))) -> a :=
  (fun (a : Type) (b : (a) -> Type) => ((@sigT_rect) (a) (b) ((fun (_ : ((@sigT) (a) (b))) => a)) ((fun (pa : a) (_ : ((b) (pa))) => pa)))).

Definition Sigma_proj2 : forall (a : Type), forall (b : (a) -> Type), forall (p : ((@sigT) (a) (b))), ((b) (((@Sigma_proj1) (a) (b) (p)))) :=
  (fun (a : Type) (b : (a) -> Type) => ((@sigT_rect) (a) (b) ((fun (p : ((@sigT) (a) (b))) => ((b) (((@Sigma_proj1) (a) (b) (p)))))) ((fun (pa : a) (pb : ((b) (pa))) => pb)))).

(* Prelude.CompM was skipped *)

(* Prelude.returnM was skipped *)

(* Prelude.bindM was skipped *)

(* Prelude.composeM was skipped *)

(* Prelude.errorM was skipped *)

(* Prelude.fixM was skipped *)

Inductive LetRecType : Type :=
| LRT_Ret : (Type) -> ((@LetRecType))
| LRT_Fun : forall (a : Type), ((a) -> ((@LetRecType))) -> ((@LetRecType))
.

Definition lrtToType : (((@LetRecType))) -> Type :=
  (fun (lrt : ((@LetRecType))) => ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (lrt))).

Definition lrtToFlatArgs : (((@LetRecType))) -> Type :=
  (fun (lrt : ((@LetRecType))) => ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (_ : Type) => unit)) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => ((@sigT) (a) (b)))) (lrt))).

Definition lrtToFlatRet : forall (lrt : ((@LetRecType))), (((@lrtToFlatArgs) (lrt))) -> Type :=
  (fun (lrt : ((@LetRecType))) => ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => (((@lrtToFlatArgs) (lrt))) -> Type)) ((fun (a : Type) (_ : unit) => a)) ((fun (a : Type) (lrtF : (a) -> ((@LetRecType))) (retF : forall (x : a), (((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (_ : Type) => unit)) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => ((@sigT) (a) (b)))) (((lrtF) (x))))) -> Type) (args : ((@sigT) (a) ((fun (x : a) => ((@lrtToFlatArgs) (((lrtF) (x)))))))) => ((retF) (((@Sigma_proj1) (a) ((fun (x : a) => ((@lrtToFlatArgs) (((lrtF) (x)))))) (args))) (((@Sigma_proj2) (a) ((fun (x : a) => ((@lrtToFlatArgs) (((lrtF) (x)))))) (args)))))) (lrt))).

Definition lrtToFlatType : (((@LetRecType))) -> Type :=
  (fun (lrt : ((@LetRecType))) => forall (args : ((@lrtToFlatArgs) (lrt))), ((CompM) (((@lrtToFlatRet) (lrt) (args))))).

Definition flattenLRTFun : forall (lrt : ((@LetRecType))), (((@lrtToType) (lrt))) -> ((@lrtToFlatType) (lrt)) :=
  (fun (lrt : ((@LetRecType))) => ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => (((@lrtToType) (lrt))) -> ((@lrtToFlatType) (lrt)))) ((fun (b : Type) (f : ((CompM) (b))) (_ : unit) => f)) ((fun (a : Type) (lrtF : (a) -> ((@LetRecType))) (restF : forall (x : a), (((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (((lrtF) (x))))) -> forall (args : ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (_ : Type) => unit)) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => ((@sigT) (a) (b)))) (((lrtF) (x))))), ((CompM) (((@lrtToFlatRet) (((lrtF) (x))) (args))))) (f : forall (x : a), ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (((lrtF) (x))))) (args : ((@sigT) (a) ((fun (_ : a) => ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (_ : Type) => unit)) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => ((@sigT) (a) (b)))) (((lrtF) (_)))))))) => ((restF) (((@Sigma_proj1) (a) ((fun (x : a) => ((@lrtToFlatArgs) (((lrtF) (x)))))) (args))) (((f) (((@Sigma_proj1) (a) ((fun (x : a) => ((@lrtToFlatArgs) (((lrtF) (x)))))) (args))))) (((@Sigma_proj2) (a) ((fun (x : a) => ((@lrtToFlatArgs) (((lrtF) (x)))))) (args)))))) (lrt))).

Definition unflattenLRTFun : forall (lrt : ((@LetRecType))), (((@lrtToFlatType) (lrt))) -> ((@lrtToType) (lrt)) :=
  (fun (lrt : ((@LetRecType))) => ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => (((@lrtToFlatType) (lrt))) -> ((@lrtToType) (lrt)))) ((fun (b : Type) (f : (unit) -> ((CompM) (b))) => ((f) (tt)))) ((fun (a : Type) (lrtF : (a) -> ((@LetRecType))) (restF : forall (x : a), (forall (args : ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (_ : Type) => unit)) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => ((@sigT) (a) (b)))) (((lrtF) (x))))), ((CompM) (((@lrtToFlatRet) (((lrtF) (x))) (args))))) -> ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (((lrtF) (x))))) (f : forall (args : ((@sigT) (a) ((fun (_ : a) => ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (_ : Type) => unit)) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => ((@sigT) (a) (b)))) (((lrtF) (_)))))))), ((CompM) (((@lrtToFlatRet) (((@LRT_Fun) (a) (lrtF))) (args))))) (x : a) => ((restF) (x) ((fun (args : ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (_ : Type) => unit)) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => ((@sigT) (a) (b)))) (((lrtF) (x))))) => ((f) (((@existT) (a) ((fun (y : a) => ((@lrtToFlatArgs) (((lrtF) (y)))))) (x) (args))))))))) (lrt))).

Inductive LetRecTypes : Type :=
| LRT_Nil : ((@LetRecTypes))
| LRT_Cons : (((@LetRecType))) -> (((@LetRecTypes))) -> ((@LetRecTypes))
.

Definition lrtPi : (((@LetRecTypes))) -> (Type) -> Type :=
  (fun (lrts : ((@LetRecTypes))) (b : Type) => ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (b) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => (((@lrtToType) (lrt))) -> rest)) (lrts))).

Definition lrtTupleType : (((@LetRecTypes))) -> Type :=
  (fun (lrts : ((@LetRecTypes))) => ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))).

Definition lrtLambda : forall (lrts : ((@LetRecTypes))), forall (B : Type), ((((@lrtTupleType) (lrts))) -> B) -> ((@lrtPi) (lrts) (B)) :=
  (fun (top_lrts : ((@LetRecTypes))) (B : Type) => ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => ((((@lrtTupleType) (lrts))) -> B) -> ((@lrtPi) (lrts) (B)))) ((fun (F : (unit) -> B) => ((F) (tt)))) ((fun (lrt : ((@LetRecType))) (lrts : ((@LetRecTypes))) (rest : ((((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))) -> B) -> ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (B) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => (((@lrtToType) (lrt))) -> rest)) (lrts))) (F : (((prod) (((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (lrt))) (((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))))) -> B) (f : ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (lrt))) => ((rest) ((fun (fs : ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))) => ((F) (((pair) (f) (fs))))))))) (top_lrts))).

Definition lrtApply : forall (lrts : ((@LetRecTypes))), forall (B : Type), (((@lrtPi) (lrts) (B))) -> (((@lrtTupleType) (lrts))) -> B :=
  (fun (top_lrts : ((@LetRecTypes))) (B : Type) => ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => (((@lrtPi) (lrts) (B))) -> (((@lrtTupleType) (lrts))) -> B)) ((fun (F : B) (_ : unit) => F)) ((fun (lrt : ((@LetRecType))) (lrts : ((@LetRecTypes))) (rest : (((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (B) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => (((@lrtToType) (lrt))) -> rest)) (lrts))) -> (((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))) -> B) (F : (((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (lrt))) -> ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (B) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => (((@lrtToType) (lrt))) -> rest)) (lrts))) (fs : ((prod) (((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (lrt))) (((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))))) => ((rest) (((F) (((SAWCoreScaffolding.fst) (fs))))) (((SAWCoreScaffolding.snd) (fs)))))) (top_lrts))).

Definition multiArgFixM : forall (lrt : ((@LetRecType))), ((((@lrtToType) (lrt))) -> ((@lrtToType) (lrt))) -> ((@lrtToType) (lrt)) :=
  (fun (lrt : ((@LetRecType))) (F : (((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (lrt))) -> ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (lrt))) => ((@unflattenLRTFun) (lrt) (((((@fixM) (CompM) (_))) (((@lrtToFlatArgs) (lrt))) (((@lrtToFlatRet) (lrt))) ((fun (f : forall (args : ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (_ : Type) => unit)) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => ((@sigT) (a) (b)))) (lrt))), ((CompM) (((@lrtToFlatRet) (lrt) (args))))) => ((@flattenLRTFun) (lrt) (((F) (((@unflattenLRTFun) (lrt) (f)))))))))))).

Definition multiTupleFixM : forall (lrts : ((@LetRecTypes))), ((((@lrtTupleType) (lrts))) -> ((@lrtTupleType) (lrts))) -> ((@lrtTupleType) (lrts)) :=
  (fun (top_lrts : ((@LetRecTypes))) => ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => ((((@lrtTupleType) (lrts))) -> ((@lrtTupleType) (lrts))) -> ((@lrtTupleType) (lrts)))) ((fun (_ : (unit) -> unit) => tt)) ((fun (lrt : ((@LetRecType))) (lrts : ((@LetRecTypes))) (restF : ((((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))) -> ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))) -> ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))) (F : (((prod) (((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (lrt))) (((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))))) -> ((prod) (((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (lrt))) (((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))))) => ((pair) (((@multiArgFixM) (lrt) ((fun (f : ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (lrt))) => ((SAWCoreScaffolding.fst) (((F) (((pair) (f) (((restF) ((fun (fs : ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))) => ((SAWCoreScaffolding.snd) (((F) (((pair) (f) (fs))))))))))))))))))) (((restF) ((fun (fs : ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))) => ((SAWCoreScaffolding.snd) (((F) (((pair) (((@multiArgFixM) (lrt) ((fun (f : ((SAWCorePrelude.LetRecType_rect) ((fun (lrt : ((@LetRecType))) => Type)) ((fun (b : Type) => ((CompM) (b)))) ((fun (a : Type) (_ : (a) -> ((@LetRecType))) (b : (a) -> Type) => forall (x : a), ((b) (x)))) (lrt))) => ((SAWCoreScaffolding.fst) (((F) (((pair) (f) (((restF) ((fun (fs : ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))) => ((SAWCoreScaffolding.snd) (((F) (((pair) (f) (fs))))))))))))))))))) (fs))))))))))))) (top_lrts))).

Definition multiFixM : forall (lrts : ((@LetRecTypes))), (((@lrtPi) (lrts) (((@lrtTupleType) (lrts))))) -> ((@lrtTupleType) (lrts)) :=
  (fun (lrts : ((@LetRecTypes))) (F : ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (((@lrtTupleType) (lrts))) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => (((@lrtToType) (lrt))) -> rest)) (lrts))) => ((@multiTupleFixM) (lrts) ((fun (fs : ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (unit) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => ((prod) (((@lrtToType) (lrt))) (rest)))) (lrts))) => ((@lrtApply) (lrts) (((@lrtTupleType) (lrts))) (F) (fs)))))).

Definition letRecM : forall (lrts : ((@LetRecTypes))), forall (B : Type), (((@lrtPi) (lrts) (((@lrtTupleType) (lrts))))) -> (((@lrtPi) (lrts) (((CompM) (B))))) -> ((CompM) (B)) :=
  (fun (lrts : ((@LetRecTypes))) (B : Type) (F : ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (((@lrtTupleType) (lrts))) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => (((@lrtToType) (lrt))) -> rest)) (lrts))) (body : ((SAWCorePrelude.LetRecTypes_rect) ((fun (lrts : ((@LetRecTypes))) => Type)) (((CompM) (B))) ((fun (lrt : ((@LetRecType))) (_ : ((@LetRecTypes))) (rest : Type) => (((@lrtToType) (lrt))) -> rest)) (lrts))) => ((@lrtApply) (lrts) (((CompM) (B))) (body) (((@multiFixM) (lrts) (F))))).

Definition letRecM1 : forall (a : Type), forall (b : Type), forall (c : Type), (((a) -> ((CompM) (b))) -> (a) -> ((CompM) (b))) -> (((a) -> ((CompM) (b))) -> ((CompM) (c))) -> ((CompM) (c)) :=
  (fun (a : Type) (b : Type) (c : Type) (fn : ((a) -> ((CompM) (b))) -> (a) -> ((CompM) (b))) (body : ((a) -> ((CompM) (b))) -> ((CompM) (c))) => ((@letRecM) (((@LRT_Cons) (((@LRT_Fun) (a) ((fun (_ : a) => ((@LRT_Ret) (b)))))) (((@LRT_Nil))))) (c) ((fun (f : (a) -> ((CompM) (b))) => ((pair) (((fn) (f))) (tt)))) ((fun (f : (a) -> ((CompM) (b))) => ((body) (f)))))).

(* Prelude.test_fun0 was skipped *)

(* Prelude.test_fun1 was skipped *)

(* Prelude.test_fun2 was skipped *)

(* Prelude.test_fun3 was skipped *)

(* Prelude.test_fun4 was skipped *)

(* Prelude.test_fun5 was skipped *)

(* Prelude.test_fun6 was skipped *)

Inductive W64List : Type :=
| W64Nil : ((@W64List))
| W64Cons : (((@bitvector) (64))) -> (((@W64List))) -> ((@W64List))
.

Definition unfoldedW64List : Type :=
  ((@Either) (unit) (((prod) (((@sigT) (((@bitvector) (64))) ((fun (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) => unit)))) (((prod) (((@W64List))) (unit)))))).

Definition unfoldW64List : (((@W64List))) -> ((@unfoldedW64List)) :=
  (fun (l : ((@W64List))) => ((SAWCorePrelude.W64List_rect) ((fun (_ : ((@W64List))) => ((@unfoldedW64List)))) (((@Left) (unit) (((prod) (((@sigT) (((@bitvector) (64))) ((fun (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) => unit)))) (((prod) (((@W64List))) (unit))))) (tt))) ((fun (bv : ((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) (l' : ((@W64List))) (_ : ((@Either) (unit) (((prod) (((@sigT) (((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) ((fun (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) => unit)))) (((prod) (((@W64List))) (unit))))))) => ((@Right) (unit) (((prod) (((@sigT) (((@bitvector) (64))) ((fun (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) => unit)))) (((prod) (((@W64List))) (unit))))) (((pair) (((@existT) (((@bitvector) (64))) ((fun (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) => unit)) (bv) (tt))) (((pair) (l') (tt)))))))) (l))).

Definition foldW64List : (((@unfoldedW64List))) -> ((@W64List)) :=
  ((@either) (unit) (((prod) (((@sigT) (((@bitvector) (64))) ((fun (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) => unit)))) (((prod) (((@W64List))) (unit))))) (((@W64List))) ((fun (_ : unit) => ((@W64Nil)))) ((fun (bv_l : ((prod) (((@sigT) (((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) ((fun (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) => unit)))) (((prod) (((@W64List))) (unit))))) => ((@W64Cons) (((@Sigma_proj1) (((@bitvector) (64))) ((fun (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (64) (((@SAWCoreScaffolding.Bool))))) => unit)) (((SAWCoreScaffolding.fst) (bv_l))))) (((SAWCoreScaffolding.fst) (((SAWCoreScaffolding.snd) (bv_l))))))))).

Inductive TrueP : Prop :=
| intro_TrueP : ((@TrueP))
.

Inductive FalseP : Prop :=
.

Inductive TpDesc : Type :=
| TpDesc_Empty : ((@TpDesc))
| TpDesc_Unit : ((@TpDesc))
| TpDesc_Bool : ((@TpDesc))
| TpDesc_Nat : ((@TpDesc))
| TpDesc_BV : (((@SAWCoreScaffolding.Nat))) -> ((@TpDesc))
| TpDesc_Pair : (((@TpDesc))) -> (((@TpDesc))) -> ((@TpDesc))
.

Definition interpTpDesc : (((@TpDesc))) -> Type :=
  (fun (tp : ((@TpDesc))) => ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))).

Inductive IndDesc : Type :=
| IndDesc_Type : forall (tp : ((@TpDesc))), ((@IndDesc))
| IndDesc_Var : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))
| IndDesc_Pair : (((@IndDesc))) -> (((@IndDesc))) -> ((@IndDesc))
| IndDesc_Either : (((@IndDesc))) -> (((@IndDesc))) -> ((@IndDesc))
| IndDesc_Sigma : forall (tp : ((@TpDesc))), ((((@interpTpDesc) (tp))) -> ((@IndDesc))) -> ((@IndDesc))
| IndDesc_BVVec : forall (n : ((@SAWCoreScaffolding.Nat))), (((@bitvector) (n))) -> (((@IndDesc))) -> ((@IndDesc))
| IndDesc_Ind : (((@IndDesc))) -> ((@IndDesc))
.

Inductive IndDescs : Type :=
| IndDescs_Nil : ((@IndDescs))
| IndDescs_Cons : (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs))
.

Definition IndDescs1 : (((@IndDesc))) -> ((@IndDescs)) :=
  (fun (d : ((@IndDesc))) => ((@IndDescs_Cons) (d) (((@IndDescs_Nil))))).

Definition IndDescs2 : (((@IndDesc))) -> (((@IndDesc))) -> ((@IndDescs)) :=
  (fun (d1 : ((@IndDesc))) (d2 : ((@IndDesc))) => ((@IndDescs_Cons) (d1) (((@IndDescs_Cons) (d2) (((@IndDescs_Nil))))))).

Definition unconsIndDescs : (((@IndDescs))) -> ((prod) (((@IndDesc))) (((@IndDescs)))) :=
  (fun (descs : ((@IndDescs))) => ((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((prod) (((@IndDesc))) (((@IndDescs)))))) (((pair) (((@IndDesc_Type) (((@TpDesc_Empty))))) (((@IndDescs_Nil))))) ((fun (desc : ((@IndDesc))) (descs : ((@IndDescs))) (_ : ((prod) (((@IndDesc))) (((@IndDescs))))) => ((pair) (desc) (descs)))) (descs))).

Definition dropIndDescs : (((@IndDescs))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDescs)) :=
  (fun (ds : ((@IndDescs))) (i : ((@SAWCoreScaffolding.Nat))) => ((@Nat__rec) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i) (ds))).

Definition nthIndDesc : (((@IndDescs))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)) :=
  (fun (descs : ((@IndDescs))) (n : ((@SAWCoreScaffolding.Nat))) => ((SAWCoreScaffolding.fst) (((@unconsIndDescs) (((@dropIndDescs) (descs) (n))))))).

Inductive IndElem : forall (_ : ((@IndDescs))), forall (_ : ((@IndDesc))), Type :=
| IElem_Const : forall (descs : ((@IndDescs))), forall (tp : ((@TpDesc))), (((@interpTpDesc) (tp))) -> ((@IndElem) (descs) (((@IndDesc_Type) (tp))))
| IElem_Var : forall (descs : ((@IndDescs))), forall (i : ((@SAWCoreScaffolding.Nat))), (((@IndElem) (((@dropIndDescs) (descs) (i))) (((@nthIndDesc) (descs) (i))))) -> ((@IndElem) (descs) (((@IndDesc_Var) (i))))
| IElem_Pair : forall (descs : ((@IndDescs))), forall (desc1 : ((@IndDesc))), forall (desc2 : ((@IndDesc))), (((@IndElem) (descs) (desc1))) -> (((@IndElem) (descs) (desc2))) -> ((@IndElem) (descs) (((@IndDesc_Pair) (desc1) (desc2))))
| IElem_Left : forall (descs : ((@IndDescs))), forall (desc1 : ((@IndDesc))), forall (desc2 : ((@IndDesc))), (((@IndElem) (descs) (desc1))) -> ((@IndElem) (descs) (((@IndDesc_Either) (desc1) (desc2))))
| IElem_Right : forall (descs : ((@IndDescs))), forall (desc1 : ((@IndDesc))), forall (desc2 : ((@IndDesc))), (((@IndElem) (descs) (desc2))) -> ((@IndElem) (descs) (((@IndDesc_Either) (desc1) (desc2))))
| IElem_Exists : forall (descs : ((@IndDescs))), forall (tp : ((@TpDesc))), forall (desc : (((@interpTpDesc) (tp))) -> ((@IndDesc))), forall (x : ((@interpTpDesc) (tp))), (((@IndElem) (descs) (((desc) (x))))) -> ((@IndElem) (descs) (((@IndDesc_Sigma) (tp) (desc))))
| IElem_BVVec : forall (descs : ((@IndDescs))), forall (desc : ((@IndDesc))), forall (n : ((@SAWCoreScaffolding.Nat))), forall (len : ((@bitvector) (n))), ((((@bitvector) (n))) -> ((@IndElem) (descs) (desc))) -> ((@IndElem) (descs) (((@IndDesc_BVVec) (n) (len) (desc))))
| IElem_Ind : forall (descs : ((@IndDescs))), forall (desc : ((@IndDesc))), (((@IndElem) (((@IndDescs_Cons) (desc) (descs))) (desc))) -> ((@IndElem) (descs) (((@IndDesc_Ind) (desc))))
.

Definition liftIndDescVar : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  ((@Nat_cases2) (((@SAWCoreScaffolding.Nat))) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (i)))) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Zero)))) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (_ : ((@SAWCoreScaffolding.Nat))) (rec_result : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (rec_result))))).

Definition liftIndDesc : (((@SAWCoreScaffolding.Nat))) -> (((@IndDesc))) -> ((@IndDesc)) :=
  (fun (k_top : ((@SAWCoreScaffolding.Nat))) (desc : ((@IndDesc))) => ((((SAWCorePrelude.IndDesc_rect) ((fun (_ : ((@IndDesc))) => (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)))) ((fun (tp : ((@TpDesc))) (_ : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Type) (tp)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Var) (((@liftIndDescVar) (k) (i)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Pair) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Either) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (tp : ((@TpDesc))) (_ : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (lift_f : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Sigma) (tp) ((fun (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((lift_f) (x) (k))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_BVVec) (n) (len) (((lift_d) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Ind) (((lift_d) (((@SAWCoreScaffolding.Succ) (k)))))))) (desc))) (k_top))).

Definition liftIndDescs : (((@SAWCoreScaffolding.Nat))) -> (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs)) :=
  ((@Nat_cases) ((((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs))) ((fun (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (d) (ds)))) ((fun (k : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs))) (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (((@liftIndDesc) (((@SAWCoreScaffolding.Succ) (k))) (((SAWCoreScaffolding.fst) (((@unconsIndDescs) (ds))))))) (((rec) (d) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds))))))))))).

Axiom liftIndElemVar : forall (ds : ((@IndDescs))), forall (i : ((@SAWCoreScaffolding.Nat))), (((@IndElem) (((@dropIndDescs) (ds) (i))) (((@nthIndDesc) (ds) (i))))) -> (forall (k : ((@SAWCoreScaffolding.Nat))), forall (d_l : ((@IndDesc))), ((@IndElem) (((@liftIndDescs) (k) (d_l) (((@dropIndDescs) (ds) (i))))) (((@liftIndDesc) (k) (((@nthIndDesc) (ds) (i))))))) -> forall (k : ((@SAWCoreScaffolding.Nat))), forall (d_l : ((@IndDesc))), ((@IndElem) (((@dropIndDescs) (((@liftIndDescs) (k) (d_l) (ds))) (((@liftIndDescVar) (k) (i))))) (((@nthIndDesc) (((@liftIndDescs) (k) (d_l) (ds))) (((@liftIndDescVar) (k) (i)))))) .

Axiom FIXME_INCONSISTENT : forall (a : Type), a .

Definition liftIndElem : forall (ds : ((@IndDescs))), forall (d : ((@IndDesc))), (((@IndElem) (ds) (d))) -> forall (k : ((@SAWCoreScaffolding.Nat))), forall (d_l : ((@IndDesc))), ((@IndElem) (((@liftIndDescs) (k) (d_l) (ds))) (((@liftIndDesc) (k) (d)))) :=
  (fun (ds_top : ((@IndDescs))) (d_top : ((@IndDesc))) (elem_top : ((@IndElem) (ds_top) (d_top))) => ((SAWCorePrelude.IndElem_rect) ((fun (ds : ((@IndDescs))) (d : ((@IndDesc))) (_ : ((@IndElem) (ds) (d))) => forall (k : ((@SAWCoreScaffolding.Nat))), forall (d_l : ((@IndDesc))), ((@IndElem) (((@liftIndDescs) (k) (d_l) (ds))) (((@liftIndDesc) (k) (d)))))) ((fun (ds : ((@IndDescs))) (tp : ((@TpDesc))) (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) (k : ((@SAWCoreScaffolding.Nat))) (d_l : ((@IndDesc))) => ((@IElem_Const) (((@liftIndDescs) (k) (d_l) (ds))) (tp) (x)))) ((fun (ds : ((@IndDescs))) (i : ((@SAWCoreScaffolding.Nat))) (elem : ((@IndElem) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))) (((SAWCoreScaffolding.fst) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((prod) (((@IndDesc))) (((@IndDescs)))))) (((pair) (((@IndDesc_Type) (((@TpDesc_Empty))))) (((@IndDescs_Nil))))) ((fun (desc : ((@IndDesc))) (descs : ((@IndDescs))) (_ : ((prod) (((@IndDesc))) (((@IndDescs))))) => ((pair) (desc) (descs)))) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))))))))) (rec : forall (k' : ((@SAWCoreScaffolding.Nat))), forall (d_l' : ((@IndDesc))), ((@IndElem) (((((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs)))) ((fun (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (d) (ds)))) ((fun (k : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs))) (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (((@liftIndDesc) (((@SAWCoreScaffolding.Succ) (k))) (((SAWCoreScaffolding.fst) (((@unconsIndDescs) (ds))))))) (((rec) (d) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))))) (k'))) (d_l') (((@dropIndDescs) (ds) (i))))) (((((SAWCorePrelude.IndDesc_rect) ((fun (_ : ((@IndDesc))) => (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)))) ((fun (tp : ((@TpDesc))) (_ : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Type) (tp)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Var) (((@liftIndDescVar) (k) (i)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Pair) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Either) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (tp : ((@TpDesc))) (_ : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (lift_f : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Sigma) (tp) ((fun (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((lift_f) (x) (k))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_BVVec) (n) (len) (((lift_d) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Ind) (((lift_d) (((@SAWCoreScaffolding.Succ) (k)))))))) (((SAWCoreScaffolding.fst) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((prod) (((@IndDesc))) (((@IndDescs)))))) (((pair) (((@IndDesc_Type) (((@TpDesc_Empty))))) (((@IndDescs_Nil))))) ((fun (desc : ((@IndDesc))) (descs : ((@IndDescs))) (_ : ((prod) (((@IndDesc))) (((@IndDescs))))) => ((pair) (desc) (descs)))) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))))))))) (k'))))) (k : ((@SAWCoreScaffolding.Nat))) (d_l : ((@IndDesc))) => ((@IElem_Var) (((@liftIndDescs) (k) (d_l) (ds))) (((@liftIndDescVar) (k) (i))) (((@liftIndElemVar) (ds) (i) (elem) (rec) (k) (d_l)))))) ((fun (ds : ((@IndDescs))) (d1 : ((@IndDesc))) (d2 : ((@IndDesc))) (_ : ((@IndElem) (ds) (d1))) (rec1 : forall (k' : ((@SAWCoreScaffolding.Nat))), forall (d_l' : ((@IndDesc))), ((@IndElem) (((((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs)))) ((fun (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (d) (ds)))) ((fun (k : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs))) (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (((@liftIndDesc) (((@SAWCoreScaffolding.Succ) (k))) (((SAWCoreScaffolding.fst) (((@unconsIndDescs) (ds))))))) (((rec) (d) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))))) (k'))) (d_l') (ds))) (((((SAWCorePrelude.IndDesc_rect) ((fun (_ : ((@IndDesc))) => (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)))) ((fun (tp : ((@TpDesc))) (_ : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Type) (tp)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Var) (((@liftIndDescVar) (k) (i)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Pair) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Either) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (tp : ((@TpDesc))) (_ : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (lift_f : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Sigma) (tp) ((fun (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((lift_f) (x) (k))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_BVVec) (n) (len) (((lift_d) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Ind) (((lift_d) (((@SAWCoreScaffolding.Succ) (k)))))))) (d1))) (k'))))) (_ : ((@IndElem) (ds) (d2))) (rec2 : forall (k' : ((@SAWCoreScaffolding.Nat))), forall (d_l' : ((@IndDesc))), ((@IndElem) (((((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs)))) ((fun (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (d) (ds)))) ((fun (k : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs))) (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (((@liftIndDesc) (((@SAWCoreScaffolding.Succ) (k))) (((SAWCoreScaffolding.fst) (((@unconsIndDescs) (ds))))))) (((rec) (d) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))))) (k'))) (d_l') (ds))) (((((SAWCorePrelude.IndDesc_rect) ((fun (_ : ((@IndDesc))) => (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)))) ((fun (tp : ((@TpDesc))) (_ : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Type) (tp)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Var) (((@liftIndDescVar) (k) (i)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Pair) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Either) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (tp : ((@TpDesc))) (_ : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (lift_f : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Sigma) (tp) ((fun (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((lift_f) (x) (k))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_BVVec) (n) (len) (((lift_d) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Ind) (((lift_d) (((@SAWCoreScaffolding.Succ) (k)))))))) (d2))) (k'))))) (k : ((@SAWCoreScaffolding.Nat))) (d_l : ((@IndDesc))) => ((@IElem_Pair) (((@liftIndDescs) (k) (d_l) (ds))) (((@liftIndDesc) (k) (d1))) (((@liftIndDesc) (k) (d2))) (((rec1) (k) (d_l))) (((rec2) (k) (d_l)))))) ((fun (ds : ((@IndDescs))) (d1 : ((@IndDesc))) (d2 : ((@IndDesc))) (_ : ((@IndElem) (ds) (d1))) (rec1 : forall (k' : ((@SAWCoreScaffolding.Nat))), forall (d_l' : ((@IndDesc))), ((@IndElem) (((((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs)))) ((fun (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (d) (ds)))) ((fun (k : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs))) (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (((@liftIndDesc) (((@SAWCoreScaffolding.Succ) (k))) (((SAWCoreScaffolding.fst) (((@unconsIndDescs) (ds))))))) (((rec) (d) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))))) (k'))) (d_l') (ds))) (((((SAWCorePrelude.IndDesc_rect) ((fun (_ : ((@IndDesc))) => (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)))) ((fun (tp : ((@TpDesc))) (_ : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Type) (tp)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Var) (((@liftIndDescVar) (k) (i)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Pair) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Either) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (tp : ((@TpDesc))) (_ : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (lift_f : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Sigma) (tp) ((fun (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((lift_f) (x) (k))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_BVVec) (n) (len) (((lift_d) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Ind) (((lift_d) (((@SAWCoreScaffolding.Succ) (k)))))))) (d1))) (k'))))) (k : ((@SAWCoreScaffolding.Nat))) (d_l : ((@IndDesc))) => ((@IElem_Left) (((@liftIndDescs) (k) (d_l) (ds))) (((@liftIndDesc) (k) (d1))) (((@liftIndDesc) (k) (d2))) (((rec1) (k) (d_l)))))) ((fun (ds : ((@IndDescs))) (d1 : ((@IndDesc))) (d2 : ((@IndDesc))) (_ : ((@IndElem) (ds) (d2))) (rec2 : forall (k' : ((@SAWCoreScaffolding.Nat))), forall (d_l' : ((@IndDesc))), ((@IndElem) (((((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs)))) ((fun (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (d) (ds)))) ((fun (k : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs))) (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (((@liftIndDesc) (((@SAWCoreScaffolding.Succ) (k))) (((SAWCoreScaffolding.fst) (((@unconsIndDescs) (ds))))))) (((rec) (d) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))))) (k'))) (d_l') (ds))) (((((SAWCorePrelude.IndDesc_rect) ((fun (_ : ((@IndDesc))) => (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)))) ((fun (tp : ((@TpDesc))) (_ : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Type) (tp)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Var) (((@liftIndDescVar) (k) (i)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Pair) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Either) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (tp : ((@TpDesc))) (_ : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (lift_f : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Sigma) (tp) ((fun (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((lift_f) (x) (k))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_BVVec) (n) (len) (((lift_d) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Ind) (((lift_d) (((@SAWCoreScaffolding.Succ) (k)))))))) (d2))) (k'))))) (k : ((@SAWCoreScaffolding.Nat))) (d_l : ((@IndDesc))) => ((@IElem_Right) (((@liftIndDescs) (k) (d_l) (ds))) (((@liftIndDesc) (k) (d1))) (((@liftIndDesc) (k) (d2))) (((rec2) (k) (d_l)))))) ((fun (ds : ((@IndDescs))) (tp : ((@TpDesc))) (d : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) (_ : ((@IndElem) (ds) (((d) (x))))) (rec : forall (k' : ((@SAWCoreScaffolding.Nat))), forall (d_l' : ((@IndDesc))), ((@IndElem) (((((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs)))) ((fun (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (d) (ds)))) ((fun (k : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs))) (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (((@liftIndDesc) (((@SAWCoreScaffolding.Succ) (k))) (((SAWCoreScaffolding.fst) (((@unconsIndDescs) (ds))))))) (((rec) (d) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))))) (k'))) (d_l') (ds))) (((((SAWCorePrelude.IndDesc_rect) ((fun (_ : ((@IndDesc))) => (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)))) ((fun (tp : ((@TpDesc))) (_ : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Type) (tp)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Var) (((@liftIndDescVar) (k) (i)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Pair) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Either) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (tp : ((@TpDesc))) (_ : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (lift_f : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Sigma) (tp) ((fun (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((lift_f) (x) (k))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_BVVec) (n) (len) (((lift_d) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Ind) (((lift_d) (((@SAWCoreScaffolding.Succ) (k)))))))) (((d) (x))))) (k'))))) (k : ((@SAWCoreScaffolding.Nat))) (d_l : ((@IndDesc))) => ((@IElem_Exists) (((@liftIndDescs) (k) (d_l) (ds))) (tp) ((fun (y : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((@liftIndDesc) (k) (((d) (y)))))) (x) (((rec) (k) (d_l)))))) ((fun (ds : ((@IndDescs))) (d : ((@IndDesc))) (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@IndElem) (ds) (d))) (rec : (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) -> forall (k' : ((@SAWCoreScaffolding.Nat))), forall (d_l' : ((@IndDesc))), ((@IndElem) (((((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs)))) ((fun (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (d) (ds)))) ((fun (k : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs))) (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (((@liftIndDesc) (((@SAWCoreScaffolding.Succ) (k))) (((SAWCoreScaffolding.fst) (((@unconsIndDescs) (ds))))))) (((rec) (d) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))))) (k'))) (d_l') (ds))) (((((SAWCorePrelude.IndDesc_rect) ((fun (_ : ((@IndDesc))) => (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)))) ((fun (tp : ((@TpDesc))) (_ : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Type) (tp)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Var) (((@liftIndDescVar) (k) (i)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Pair) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Either) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (tp : ((@TpDesc))) (_ : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (lift_f : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Sigma) (tp) ((fun (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((lift_f) (x) (k))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_BVVec) (n) (len) (((lift_d) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Ind) (((lift_d) (((@SAWCoreScaffolding.Succ) (k)))))))) (d))) (k'))))) (k : ((@SAWCoreScaffolding.Nat))) (d_l : ((@IndDesc))) => ((@IElem_BVVec) (((@liftIndDescs) (k) (d_l) (ds))) (((@liftIndDesc) (k) (d))) (n) (len) ((fun (bv : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) => ((rec) (bv) (k) (d_l))))))) ((fun (ds : ((@IndDescs))) (d : ((@IndDesc))) (_ : ((@IndElem) (((@IndDescs_Cons) (d) (ds))) (d))) (rec : forall (k' : ((@SAWCoreScaffolding.Nat))), forall (d_l' : ((@IndDesc))), ((@IndElem) (((((SAWCoreScaffolding.Nat_rect) ((fun (n : ((@SAWCoreScaffolding.Nat))) => (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs)))) ((fun (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (d) (ds)))) ((fun (k : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDesc))) -> (((@IndDescs))) -> ((@IndDescs))) (d : ((@IndDesc))) (ds : ((@IndDescs))) => ((@IndDescs_Cons) (((@liftIndDesc) (((@SAWCoreScaffolding.Succ) (k))) (((SAWCoreScaffolding.fst) (((@unconsIndDescs) (ds))))))) (((rec) (d) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))))) (k'))) (d_l') (((@IndDescs_Cons) (d) (ds))))) (((((SAWCorePrelude.IndDesc_rect) ((fun (_ : ((@IndDesc))) => (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)))) ((fun (tp : ((@TpDesc))) (_ : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Type) (tp)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Var) (((@liftIndDescVar) (k) (i)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Pair) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (lift_d2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Either) (((lift_d1) (k))) (((lift_d2) (k)))))) ((fun (tp : ((@TpDesc))) (_ : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (lift_f : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Sigma) (tp) ((fun (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((lift_f) (x) (k))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_BVVec) (n) (len) (((lift_d) (k)))))) ((fun (_ : ((@IndDesc))) (lift_d : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (k : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Ind) (((lift_d) (((@SAWCoreScaffolding.Succ) (k)))))))) (d))) (k'))))) (k : ((@SAWCoreScaffolding.Nat))) (d_l : ((@IndDesc))) => ((@IElem_Ind) (((@liftIndDescs) (k) (d_l) (ds))) (((@liftIndDesc) (((@SAWCoreScaffolding.Succ) (k))) (d))) (((rec) (((@SAWCoreScaffolding.Succ) (k))) (d_l)))))) (ds_top) (d_top) (elem_top))).

Definition appendIndDescs : (((@IndDescs))) -> (((@IndDescs))) -> ((@IndDescs)) :=
  (fun (ds1 : ((@IndDescs))) (ds2 : ((@IndDescs))) => ((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds2) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds1))).

Axiom noIndElemEmpty : forall (a : Type), forall (ds : ((@IndDescs))), (((@IndElem) (ds) (((@IndDesc_Type) (((@TpDesc_Empty))))))) -> a .

Definition topLiftIndElemVar0 : forall (ds_l : ((@IndDescs))), forall (ds : ((@IndDescs))), (((@IndElem) (((@appendIndDescs) (ds) (ds_l))) (((@nthIndDesc) (ds) (0))))) -> ((@IndElem) (((@appendIndDescs) (ds) (ds_l))) (((@nthIndDesc) (((@appendIndDescs) (ds) (ds_l))) (0)))) :=
  (fun (ds_l : ((@IndDescs))) (ds_top : ((@IndDescs))) => ((SAWCorePrelude.IndDescs_rect) ((fun (ds : ((@IndDescs))) => (((@IndElem) (((@appendIndDescs) (ds) (ds_l))) (((@nthIndDesc) (ds) (0))))) -> ((@IndElem) (((@appendIndDescs) (ds) (ds_l))) (((@nthIndDesc) (((@appendIndDescs) (ds) (ds_l))) (0)))))) ((fun (elem : ((@IndElem) (ds_l) (((@IndDesc_Type) (((@TpDesc_Empty))))))) => ((@noIndElemEmpty) (((@IndElem) (ds_l) (((@nthIndDesc) (ds_l) (0))))) (ds_l) (elem)))) ((fun (d : ((@IndDesc))) (ds : ((@IndDescs))) (_ : (((@IndElem) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds))) (((SAWCoreScaffolding.fst) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((prod) (((@IndDesc))) (((@IndDescs)))))) (((pair) (((@IndDesc_Type) (((@TpDesc_Empty))))) (((@IndDescs_Nil))))) ((fun (desc : ((@IndDesc))) (descs : ((@IndDescs))) (_ : ((prod) (((@IndDesc))) (((@IndDescs))))) => ((pair) (desc) (descs)))) (ds))))))) -> ((@IndElem) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds))) (((SAWCoreScaffolding.fst) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((prod) (((@IndDesc))) (((@IndDescs)))))) (((pair) (((@IndDesc_Type) (((@TpDesc_Empty))))) (((@IndDescs_Nil))))) ((fun (desc : ((@IndDesc))) (descs : ((@IndDescs))) (_ : ((prod) (((@IndDesc))) (((@IndDescs))))) => ((pair) (desc) (descs)))) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds))))))))) (elem : ((@IndElem) (((@IndDescs_Cons) (d) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds))))) (d))) => elem)) (ds_top))).

Definition ltIndDescsLen : forall (i : ((@SAWCoreScaffolding.Nat))), forall (ds : ((@IndDescs))), Prop :=
  ((@Nat__rec) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> Prop)) ((fun (ds : ((@IndDescs))) => ((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => Prop)) (((@FalseP))) ((fun (_ : ((@IndDesc))) (_ : ((@IndDescs))) (_ : Prop) => ((@TrueP)))) (ds)))) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> Prop) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds))))))))).

Definition nthElemLtIndDescsLen : forall (i : ((@SAWCoreScaffolding.Nat))), forall (any : ((@IndDescs))), forall (ds : ((@IndDescs))), (((@IndElem) (any) (((@nthIndDesc) (ds) (i))))) -> ((@ltIndDescsLen) (i) (ds)) :=
  ((@Nat__rec) ((fun (i : ((@SAWCoreScaffolding.Nat))) => forall (any : ((@IndDescs))), forall (ds : ((@IndDescs))), (((@IndElem) (any) (((@nthIndDesc) (ds) (i))))) -> ((@ltIndDescsLen) (i) (ds)))) ((fun (any : ((@IndDescs))) (ds : ((@IndDescs))) => ((SAWCorePrelude.IndDescs_rect) ((fun (ds : ((@IndDescs))) => (((@IndElem) (any) (((@nthIndDesc) (ds) (0))))) -> ((@ltIndDescsLen) (0) (ds)))) ((fun (elem : ((@IndElem) (any) (((@IndDesc_Type) (((@TpDesc_Empty))))))) => ((@noIndElemEmpty) (((@FalseP))) (any) (elem)))) ((fun (d : ((@IndDesc))) (ds : ((@IndDescs))) (_ : (((@IndElem) (any) (((SAWCoreScaffolding.fst) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((prod) (((@IndDesc))) (((@IndDescs)))))) (((pair) (((@IndDesc_Type) (((@TpDesc_Empty))))) (((@IndDescs_Nil))))) ((fun (desc : ((@IndDesc))) (descs : ((@IndDescs))) (_ : ((prod) (((@IndDesc))) (((@IndDescs))))) => ((pair) (desc) (descs)))) (ds))))))) -> ((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => Prop)) (((@FalseP))) ((fun (_ : ((@IndDesc))) (_ : ((@IndDescs))) (_ : Prop) => ((@TrueP)))) (ds))) (_ : ((@IndElem) (any) (d))) => ((@intro_TrueP)))) (ds)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (rec : forall (any : ((@IndDescs))), forall (ds : ((@IndDescs))), (((@IndElem) (any) (((SAWCoreScaffolding.fst) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((prod) (((@IndDesc))) (((@IndDescs)))))) (((pair) (((@IndDesc_Type) (((@TpDesc_Empty))))) (((@IndDescs_Nil))))) ((fun (desc : ((@IndDesc))) (descs : ((@IndDescs))) (_ : ((prod) (((@IndDesc))) (((@IndDescs))))) => ((pair) (desc) (descs)))) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))))))))) -> ((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> Prop)) ((fun (ds : ((@IndDescs))) => ((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => Prop)) (((@FalseP))) ((fun (_ : ((@IndDesc))) (_ : ((@IndDescs))) (_ : Prop) => ((@TrueP)))) (ds)))) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> Prop) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))) (any : ((@IndDescs))) (ds : ((@IndDescs))) (elem : ((@IndElem) (any) (((SAWCoreScaffolding.fst) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((prod) (((@IndDesc))) (((@IndDescs)))))) (((pair) (((@IndDesc_Type) (((@TpDesc_Empty))))) (((@IndDescs_Nil))))) ((fun (desc : ((@IndDesc))) (descs : ((@IndDescs))) (_ : ((prod) (((@IndDesc))) (((@IndDescs))))) => ((pair) (desc) (descs)))) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds))))))))))))) => ((rec) (any) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds))))) (elem))))).

Axiom unconsAppendIndDescsEq : forall (i : ((@SAWCoreScaffolding.Nat))), forall (ds_l : ((@IndDescs))), forall (ds : ((@IndDescs))), (((@ltIndDescsLen) (i) (ds))) -> ((@SAWCoreScaffolding.EqP) (((@IndDescs))) (((@appendIndDescs) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds))))) (ds_l))) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (((@appendIndDescs) (ds) (ds_l)))))))) .

Definition dropAppendIndDescsEq : forall (i : ((@SAWCoreScaffolding.Nat))), forall (ds_l : ((@IndDescs))), forall (ds : ((@IndDescs))), (((@ltIndDescsLen) (i) (ds))) -> ((@SAWCoreScaffolding.EqP) (((@IndDescs))) (((@appendIndDescs) (((@dropIndDescs) (ds) (i))) (ds_l))) (((@dropIndDescs) (((@appendIndDescs) (ds) (ds_l))) (i)))) :=
  ((@Nat__rec) ((fun (i : ((@SAWCoreScaffolding.Nat))) => forall (ds_l : ((@IndDescs))), forall (ds : ((@IndDescs))), (((@ltIndDescsLen) (i) (ds))) -> ((@SAWCoreScaffolding.EqP) (((@IndDescs))) (((@appendIndDescs) (((@dropIndDescs) (ds) (i))) (ds_l))) (((@dropIndDescs) (((@appendIndDescs) (ds) (ds_l))) (i)))))) ((fun (ds_l : ((@IndDescs))) (ds : ((@IndDescs))) (_ : ((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => Prop)) (((@FalseP))) ((fun (_ : ((@IndDesc))) (_ : ((@IndDescs))) (_ : Prop) => ((@TrueP)))) (ds))) => ((@SAWCoreScaffolding.ReflP) (((@IndDescs))) (((@appendIndDescs) (ds) (ds_l)))))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (rec : forall (ds_l : ((@IndDescs))), forall (ds : ((@IndDescs))), (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> Prop)) ((fun (ds : ((@IndDescs))) => ((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => Prop)) (((@FalseP))) ((fun (_ : ((@IndDesc))) (_ : ((@IndDescs))) (_ : Prop) => ((@TrueP)))) (ds)))) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> Prop) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))) -> ((@SAWCoreScaffolding.EqP) (((@IndDescs))) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))))) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (((@appendIndDescs) (ds) (ds_l))))))) (ds_l : ((@IndDescs))) (ds : ((@IndDescs))) (ltLen : ((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> Prop)) ((fun (ds : ((@IndDescs))) => ((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => Prop)) (((@FalseP))) ((fun (_ : ((@IndDesc))) (_ : ((@IndDescs))) (_ : Prop) => ((@TrueP)))) (ds)))) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> Prop) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds))))))) => ((@transP) (((@IndDescs))) (((@appendIndDescs) (((@dropIndDescs) (ds) (((@SAWCoreScaffolding.Succ) (i))))) (ds_l))) (((@dropIndDescs) (((@appendIndDescs) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds))))) (ds_l))) (i))) (((@dropIndDescs) (((@appendIndDescs) (ds) (ds_l))) (((@SAWCoreScaffolding.Succ) (i))))) (((rec) (ds_l) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds))))) (ltLen))) (((@eqP_cong) (((@IndDescs))) (((@appendIndDescs) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds))))) (ds_l))) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (((@appendIndDescs) (ds) (ds_l))))))) (((@unconsAppendIndDescsEq) (((@SAWCoreScaffolding.Succ) (i))) (ds_l) (ds) (ltLen))) (((@IndDescs))) ((fun (ds' : ((@IndDescs))) => ((@dropIndDescs) (ds') (i)))))))))).

Axiom nthAppendIndDescsEq : forall (i : ((@SAWCoreScaffolding.Nat))), forall (ds_l : ((@IndDescs))), forall (ds : ((@IndDescs))), (((@ltIndDescsLen) (i) (ds))) -> ((@SAWCoreScaffolding.EqP) (((@IndDesc))) (((@nthIndDesc) (ds) (i))) (((@nthIndDesc) (((@appendIndDescs) (ds) (ds_l))) (i)))) .

Axiom dropAppendIndDescsEq_FIXME : forall (i : ((@SAWCoreScaffolding.Nat))), forall (ds_l : ((@IndDescs))), forall (ds : ((@IndDescs))), (((@ltIndDescsLen) (i) (ds))) -> ((@SAWCoreScaffolding.EqP) (((@IndDescs))) (((@appendIndDescs) (((@dropIndDescs) (ds) (i))) (ds_l))) (((@dropIndDescs) (((@appendIndDescs) (ds) (ds_l))) (i)))) .

Definition coerceIndElem : forall (ds1 : ((@IndDescs))), forall (ds2 : ((@IndDescs))), forall (d1 : ((@IndDesc))), forall (d2 : ((@IndDesc))), (((@SAWCoreScaffolding.EqP) (((@IndDescs))) (ds1) (ds2))) -> (((@SAWCoreScaffolding.EqP) (((@IndDesc))) (d1) (d2))) -> (((@IndElem) (ds1) (d1))) -> ((@IndElem) (ds2) (d2)) :=
  (fun (ds1 : ((@IndDescs))) (ds2 : ((@IndDescs))) (d1 : ((@IndDesc))) (d2 : ((@IndDesc))) (eq_ds : ((@SAWCoreScaffolding.EqP) (((@IndDescs))) (ds1) (ds2))) (eq_d : ((@SAWCoreScaffolding.EqP) (((@IndDesc))) (d1) (d2))) => ((@coerceP) (((@IndElem) (ds1) (d1))) (((@IndElem) (ds2) (d2))) (((@transP) (Type) (((@IndElem) (ds1) (d1))) (((@IndElem) (ds2) (d1))) (((@IndElem) (ds2) (d2))) (((@eqP_cong) (((@IndDescs))) (ds1) (ds2) (eq_ds) (Type) ((fun (ds : ((@IndDescs))) => ((@IndElem) (ds) (d1)))))) (((@eqP_cong) (((@IndDesc))) (d1) (d2) (eq_d) (Type) ((fun (d : ((@IndDesc))) => ((@IndElem) (ds2) (d)))))))))).

Definition topLiftIndElemVar : forall (i : ((@SAWCoreScaffolding.Nat))), forall (ds_l : ((@IndDescs))), forall (ds : ((@IndDescs))), (((@IndElem) (((@appendIndDescs) (((@dropIndDescs) (ds) (i))) (ds_l))) (((@nthIndDesc) (ds) (i))))) -> ((@IndElem) (((@dropIndDescs) (((@appendIndDescs) (ds) (ds_l))) (i))) (((@nthIndDesc) (((@appendIndDescs) (ds) (ds_l))) (i)))) :=
  (fun (i : ((@SAWCoreScaffolding.Nat))) (ds_l : ((@IndDescs))) (ds : ((@IndDescs))) (elem : ((@IndElem) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))))) (((SAWCoreScaffolding.fst) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((prod) (((@IndDesc))) (((@IndDescs)))))) (((pair) (((@IndDesc_Type) (((@TpDesc_Empty))))) (((@IndDescs_Nil))))) ((fun (desc : ((@IndDesc))) (descs : ((@IndDescs))) (_ : ((prod) (((@IndDesc))) (((@IndDescs))))) => ((pair) (desc) (descs)))) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))))))))) => ((@coerceIndElem) (((@appendIndDescs) (((@dropIndDescs) (ds) (i))) (ds_l))) (((@dropIndDescs) (((@appendIndDescs) (ds) (ds_l))) (i))) (((@nthIndDesc) (ds) (i))) (((@nthIndDesc) (((@appendIndDescs) (ds) (ds_l))) (i))) (((@dropAppendIndDescsEq_FIXME) (i) (ds_l) (ds) (((@nthElemLtIndDescsLen) (i) (((@appendIndDescs) (((@dropIndDescs) (ds) (i))) (ds_l))) (ds) (elem))))) (((@nthAppendIndDescsEq) (i) (ds_l) (ds) (((@nthElemLtIndDescsLen) (i) (((@appendIndDescs) (((@dropIndDescs) (ds) (i))) (ds_l))) (ds) (elem))))) (elem))).

Definition topLiftIndElem : forall (ds_l : ((@IndDescs))), forall (ds : ((@IndDescs))), forall (d : ((@IndDesc))), (((@IndElem) (ds) (d))) -> ((@IndElem) (((@appendIndDescs) (ds) (ds_l))) (d)) :=
  (fun (ds_l : ((@IndDescs))) (ds_top : ((@IndDescs))) (d_top : ((@IndDesc))) (elem_top : ((@IndElem) (ds_top) (d_top))) => ((SAWCorePrelude.IndElem_rect) ((fun (ds : ((@IndDescs))) (d : ((@IndDesc))) (_ : ((@IndElem) (ds) (d))) => ((@IndElem) (((@appendIndDescs) (ds) (ds_l))) (d)))) ((fun (ds : ((@IndDescs))) (tp : ((@TpDesc))) (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((@IElem_Const) (((@appendIndDescs) (ds) (ds_l))) (tp) (x)))) ((fun (ds : ((@IndDescs))) (i : ((@SAWCoreScaffolding.Nat))) (_ : ((@IndElem) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))) (((SAWCoreScaffolding.fst) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((prod) (((@IndDesc))) (((@IndDescs)))))) (((pair) (((@IndDesc_Type) (((@TpDesc_Empty))))) (((@IndDescs_Nil))))) ((fun (desc : ((@IndDesc))) (descs : ((@IndDescs))) (_ : ((prod) (((@IndDesc))) (((@IndDescs))))) => ((pair) (desc) (descs)))) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))))))))) (rec : ((@IndElem) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))))) (((SAWCoreScaffolding.fst) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((prod) (((@IndDesc))) (((@IndDescs)))))) (((pair) (((@IndDesc_Type) (((@TpDesc_Empty))))) (((@IndDescs_Nil))))) ((fun (desc : ((@IndDesc))) (descs : ((@IndDescs))) (_ : ((prod) (((@IndDesc))) (((@IndDescs))))) => ((pair) (desc) (descs)))) (((((SAWCoreScaffolding.Nat_rect) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => (((@IndDescs))) -> ((@IndDescs)))) ((fun (ds : ((@IndDescs))) => ds)) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@IndDescs))) -> ((@IndDescs))) (ds : ((@IndDescs))) => ((rec) (((SAWCoreScaffolding.snd) (((@unconsIndDescs) (ds)))))))) (i))) (ds))))))))) => ((@IElem_Var) (((@appendIndDescs) (ds) (ds_l))) (i) (((@topLiftIndElemVar) (i) (ds_l) (ds) (rec)))))) ((fun (ds : ((@IndDescs))) (d1 : ((@IndDesc))) (d2 : ((@IndDesc))) (_ : ((@IndElem) (ds) (d1))) (rec1 : ((@IndElem) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds))) (d1))) (_ : ((@IndElem) (ds) (d2))) (rec2 : ((@IndElem) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds))) (d2))) => ((@IElem_Pair) (((@appendIndDescs) (ds) (ds_l))) (d1) (d2) (rec1) (rec2)))) ((fun (ds : ((@IndDescs))) (d1 : ((@IndDesc))) (d2 : ((@IndDesc))) (_ : ((@IndElem) (ds) (d1))) (rec1 : ((@IndElem) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds))) (d1))) => ((@IElem_Left) (((@appendIndDescs) (ds) (ds_l))) (d1) (d2) (rec1)))) ((fun (ds : ((@IndDescs))) (d1 : ((@IndDesc))) (d2 : ((@IndDesc))) (_ : ((@IndElem) (ds) (d2))) (rec2 : ((@IndElem) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds))) (d2))) => ((@IElem_Right) (((@appendIndDescs) (ds) (ds_l))) (d1) (d2) (rec2)))) ((fun (ds : ((@IndDescs))) (tp : ((@TpDesc))) (d : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) (_ : ((@IndElem) (ds) (((d) (x))))) (rec : ((@IndElem) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds))) (((d) (x))))) => ((@IElem_Exists) (((@appendIndDescs) (ds) (ds_l))) (tp) (d) (x) (rec)))) ((fun (ds : ((@IndDescs))) (d : ((@IndDesc))) (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@IndElem) (ds) (d))) (rec : (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@IndElem) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds))) (d))) => ((@IElem_BVVec) (((@appendIndDescs) (ds) (ds_l))) (d) (n) (len) (rec)))) ((fun (ds : ((@IndDescs))) (d : ((@IndDesc))) (_ : ((@IndElem) (((@IndDescs_Cons) (d) (ds))) (d))) (rec : ((@IndElem) (((@IndDescs_Cons) (d) (((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@IndDescs)))) (ds_l) ((fun (d : ((@IndDesc))) (_ : ((@IndDescs))) (res : ((@IndDescs))) => ((@IndDescs_Cons) (d) (res)))) (ds))))) (d))) => ((@IElem_Ind) (((@appendIndDescs) (ds) (ds_l))) (d) (rec)))) (ds_top) (d_top) (elem_top))).

Definition topLiftIndDesc : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> (((@IndDesc))) -> ((@IndDesc)) :=
  (fun (_ : ((@SAWCoreScaffolding.Nat))) (_ : ((@SAWCoreScaffolding.Nat))) (d : ((@IndDesc))) => d).

Definition topSubstIndDescVar : (((@IndDesc))) -> (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)) :=
  (fun (top_d : ((@IndDesc))) => ((@Nat_cases) ((((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (k : ((@SAWCoreScaffolding.Nat))) => ((@if0Nat) (((@IndDesc))) (i) (((@topLiftIndDesc) (k) (0) (top_d))) (((@IndDesc_Var) (((@addNat) (i) (k)))))))) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (rec : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (i : ((@SAWCoreScaffolding.Nat))) (k : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases) (((@IndDesc))) (((@IndDesc_Var) (k))) ((fun (i' : ((@SAWCoreScaffolding.Nat))) (_ : ((@IndDesc))) => ((rec) (i') (((@SAWCoreScaffolding.Succ) (k)))))) (i)))))).

Definition topSubstIndDesc : (((@IndDesc))) -> (((@SAWCoreScaffolding.Nat))) -> (((@IndDesc))) -> ((@IndDesc)) :=
  (fun (top_d : ((@IndDesc))) (top_n : ((@SAWCoreScaffolding.Nat))) (d : ((@IndDesc))) => ((((SAWCorePrelude.IndDesc_rect) ((fun (_ : ((@IndDesc))) => (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc)))) ((fun (tp : ((@TpDesc))) (_ : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Type) (tp)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) => ((@topSubstIndDescVar) (top_d) (n) (i) (0)))) ((fun (_ : ((@IndDesc))) (rec1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (rec2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (n : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Pair) (((rec1) (n))) (((rec2) (n)))))) ((fun (_ : ((@IndDesc))) (rec1 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (_ : ((@IndDesc))) (rec2 : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (n : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Either) (((rec1) (n))) (((rec2) (n)))))) ((fun (tp : ((@TpDesc))) (_ : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (rec : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (n : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Sigma) (tp) ((fun (x : ((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) => ((rec) (x) (n))))))) ((fun (bn : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (bn) (((@SAWCoreScaffolding.Bool))))) (_ : ((@IndDesc))) (rec : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (n : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_BVVec) (bn) (len) (((rec) (n)))))) ((fun (d' : ((@IndDesc))) (rec : (((@SAWCoreScaffolding.Nat))) -> ((@IndDesc))) (n : ((@SAWCoreScaffolding.Nat))) => ((@IndDesc_Ind) (((rec) (((@SAWCoreScaffolding.Succ) (n)))))))) (d))) (top_n))).

Definition lenIndDescs : (((@IndDescs))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (ds : ((@IndDescs))) => ((SAWCorePrelude.IndDescs_rect) ((fun (_ : ((@IndDescs))) => ((@SAWCoreScaffolding.Nat)))) (0) ((fun (_ : ((@IndDesc))) (_ : ((@IndDescs))) (len : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.Succ) (len)))) (ds))).

Axiom topSubstIndElem : forall (top_d : ((@IndDesc))), forall (ds : ((@IndDescs))), forall (d : ((@IndDesc))), (((@IndElem) (((@appendIndDescs) (((@IndDescs1) (top_d))) (ds))) (d))) -> ((@IndElem) (ds) (((@topSubstIndDesc) (top_d) (((@lenIndDescs) (ds))) (d)))) .

Definition interpIndDesc : (((@IndDesc))) -> (((@IndDesc))) -> Type :=
  (fun (top_d : ((@IndDesc))) (d : ((@IndDesc))) => ((SAWCorePrelude.IndDesc_rect) ((fun (_ : ((@IndDesc))) => Type)) ((fun (tp : ((@TpDesc))) => ((@interpTpDesc) (tp)))) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@Nat_cases) (Type) (((@IndElem) (((@IndDescs1) (top_d))) (top_d))) ((fun (_ : ((@SAWCoreScaffolding.Nat))) (_ : Type) => ((@FalseP)))) (i)))) ((fun (_ : ((@IndDesc))) (a : Type) (_ : ((@IndDesc))) (b : Type) => ((prod) (a) (b)))) ((fun (_ : ((@IndDesc))) (a : Type) (_ : ((@IndDesc))) (b : Type) => ((@Either) (a) (b)))) ((fun (tp : ((@TpDesc))) (_ : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> ((@IndDesc))) (f : (((SAWCorePrelude.TpDesc_rect) ((fun (_ : ((@TpDesc))) => Type)) (((@FalseP))) (unit) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Nat))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@bitvector) (n)))) ((fun (_ : ((@TpDesc))) (a : Type) (_ : ((@TpDesc))) (b : Type) => ((prod) (a) (b)))) (tp))) -> Type) => ((@sigT) (((@interpTpDesc) (tp))) (f)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (len : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (_ : ((@IndDesc))) (a : Type) => ((@BVVec) (n) (len) (a)))) ((fun (d' : ((@IndDesc))) (_ : Type) => ((@IndElem) (((@IndDescs1) (d'))) (((@topSubstIndDesc) (top_d) (1) (d')))))) (d))).

Axiom foldIndElem : forall (top_desc : ((@IndDesc))), forall (desc : ((@IndDesc))), (((@interpIndDesc) (top_desc) (desc))) -> ((@IndElem) (((@IndDescs1) (top_desc))) (desc)) .

Axiom unfoldIndElem : forall (top_desc : ((@IndDesc))), forall (desc : ((@IndDesc))), (((@IndElem) (((@IndDescs1) (top_desc))) (desc))) -> ((@interpIndDesc) (top_desc) (desc)) .

Axiom mapIndElem : forall (d1 : ((@IndDesc))), forall (d2 : ((@IndDesc))), ((((@interpIndDesc) (d2) (d1))) -> ((@interpIndDesc) (d2) (d2))) -> (((@IndElem) (((@IndDescs1) (d1))) (d1))) -> ((@IndElem) (((@IndDescs1) (d2))) (d2)) .

(* Prelude.bveq_sameL was skipped *)

(* Prelude.bveq_sameR was skipped *)

(* Prelude.bveq_same2 was skipped *)

(* Prelude.bvNat_bvToNat was skipped *)

(* Prelude.ite_split_cong was skipped *)

(* Prelude.ite_join_cong was skipped *)

(* Prelude.map_map was skipped *)

End SAWCorePrelude.
