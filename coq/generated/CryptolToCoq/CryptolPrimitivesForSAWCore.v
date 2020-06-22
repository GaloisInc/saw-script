
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.

Import ListNotations.

Module CryptolPrimitives.

Definition const : forall (a : Type), forall (b : Type), (a) -> (b) -> a :=
  (fun (a : Type) (b : Type) (x : a) (y : b) => x).

Definition compose : forall (a : Type), forall (b : Type), forall (c : Type), ((b) -> c) -> ((a) -> b) -> (a) -> c :=
  (fun (_ : Type) (_ : Type) (_ : Type) (f : (_) -> _) (g : (_) -> _) (x : _) => ((f) (((g) (x))))).

Definition bvExp : forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCorePrelude.bitvector) (n))) -> ((@SAWCorePrelude.bitvector) (n)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreVectorsAsCoqVectors.foldr) (((@SAWCoreScaffolding.Bool))) (((@SAWCorePrelude.bitvector) (n))) (n) ((fun (b : ((@SAWCoreScaffolding.Bool))) (a : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) => if b then ((@SAWCoreVectorsAsCoqVectors.bvMul) (n) (x) (((@SAWCoreVectorsAsCoqVectors.bvMul) (n) (a) (a)))) else ((@SAWCoreVectorsAsCoqVectors.bvMul) (n) (a) (a)))) (((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (1))) (((@SAWCorePrelude.reverse) (n) (((@SAWCoreScaffolding.Bool))) (y))))).

Definition updFst : forall (a : Type), forall (b : Type), ((a) -> a) -> (((prod) (a) (b))) -> ((prod) (a) (b)) :=
  (fun (a : Type) (b : Type) (f : (a) -> a) (x : ((prod) (a) (b))) => ((pair) (((f) (((SAWCoreScaffolding.fst) (x))))) (((SAWCoreScaffolding.snd) (x))))).

Definition updSnd : forall (a : Type), forall (b : Type), ((b) -> b) -> (((prod) (a) (b))) -> ((prod) (a) (b)) :=
  (fun (a : Type) (b : Type) (f : (b) -> b) (x : ((prod) (a) (b))) => ((pair) (((SAWCoreScaffolding.fst) (x))) (((f) (((SAWCoreScaffolding.snd) (x))))))).

Inductive Num : Type :=
| TCNum : (((@SAWCoreScaffolding.Nat))) -> ((@Num))
| TCInf : ((@Num))
.

(* Cryptol.Num_rec was skipped *)

Definition getFinNat : forall (n : ((@Num))), ((@SAWCoreScaffolding.Nat)) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => ((@SAWCoreScaffolding.Nat)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => n)) (((@SAWCoreScaffolding.error) (((@SAWCoreScaffolding.Nat))) (("Unexpected Fin constraint violation!")%string))) (n))).

Definition finNumRec : forall (p : (((@Num))) -> Type), (forall (n : ((@SAWCoreScaffolding.Nat))), ((p) (((@TCNum) (n))))) -> forall (n : ((@Num))), ((p) (n)) :=
  (fun (p : (((@Num))) -> Type) (f : forall (n : ((@SAWCoreScaffolding.Nat))), ((p) (((@TCNum) (n))))) (n : ((@Num))) => ((CryptolPrimitives.Num_rect) (p) (f) (((@SAWCoreScaffolding.error) (((p) (((@TCInf))))) (("Unexpected Fin constraint violation!")%string))) (n))).

Definition finNumRec2 : forall (p : (((@Num))) -> (((@Num))) -> Type), (forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), ((p) (((@TCNum) (m))) (((@TCNum) (n))))) -> forall (m : ((@Num))), forall (n : ((@Num))), ((p) (m) (n)) :=
  (fun (p : (((@Num))) -> (((@Num))) -> Type) (f : forall (m : ((@SAWCoreScaffolding.Nat))), forall (n : ((@SAWCoreScaffolding.Nat))), ((p) (((@TCNum) (m))) (((@TCNum) (n))))) => ((@finNumRec) ((fun (m : ((@Num))) => forall (n : ((@Num))), ((p) (m) (n)))) ((fun (m : ((@SAWCoreScaffolding.Nat))) => ((@finNumRec) (((p) (((@TCNum) (m))))) (((f) (m)))))))).

Definition binaryNumFun : ((((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat))) -> ((((@SAWCoreScaffolding.Nat))) -> ((@Num))) -> ((((@SAWCoreScaffolding.Nat))) -> ((@Num))) -> (((@Num))) -> (((@Num))) -> (((@Num))) -> ((@Num)) :=
  (fun (f1 : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat))) (f2 : (((@SAWCoreScaffolding.Nat))) -> ((@Num))) (f3 : (((@SAWCoreScaffolding.Nat))) -> ((@Num))) (f4 : ((@Num))) (num1 : ((@Num))) (num2 : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (num1' : ((@Num))) => ((@Num)))) ((fun (n1 : ((@SAWCoreScaffolding.Nat))) => ((CryptolPrimitives.Num_rect) ((fun (num2' : ((@Num))) => ((@Num)))) ((fun (n2 : ((@SAWCoreScaffolding.Nat))) => ((@TCNum) (((f1) (n1) (n2)))))) (((f2) (n1))) (num2)))) (((CryptolPrimitives.Num_rect) ((fun (num2' : ((@Num))) => ((@Num)))) (f3) (f4) (num2))) (num1))).

Definition ternaryNumFun : ((((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat))) -> (((@Num))) -> (((@Num))) -> (((@Num))) -> (((@Num))) -> ((@Num)) :=
  (fun (f1 : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat))) (f2 : ((@Num))) (num1 : ((@Num))) (num2 : ((@Num))) (num3 : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (num1' : ((@Num))) => ((@Num)))) ((fun (n1 : ((@SAWCoreScaffolding.Nat))) => ((CryptolPrimitives.Num_rect) ((fun (num2' : ((@Num))) => ((@Num)))) ((fun (n2 : ((@SAWCoreScaffolding.Nat))) => ((CryptolPrimitives.Num_rect) ((fun (num3' : ((@Num))) => ((@Num)))) ((fun (n3 : ((@SAWCoreScaffolding.Nat))) => ((@TCNum) (((f1) (n1) (n2) (n3)))))) (f2) (num3)))) (f2) (num2)))) (f2) (num1))).

Definition tcWidth : (((@Num))) -> ((@Num)) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => ((@Num)))) ((fun (x : ((@SAWCoreScaffolding.Nat))) => ((@TCNum) (((@SAWCoreScaffolding.widthNat) (x)))))) (((@TCInf))) (n))).

Definition tcAdd : (((@Num))) -> (((@Num))) -> ((@Num)) :=
  ((@binaryNumFun) (((@SAWCorePrelude.addNat))) ((fun (x : ((@SAWCoreScaffolding.Nat))) => ((@TCInf)))) ((fun (y : ((@SAWCoreScaffolding.Nat))) => ((@TCInf)))) (((@TCInf)))).

Definition tcSub : (((@Num))) -> (((@Num))) -> ((@Num)) :=
  ((@binaryNumFun) (((@SAWCorePrelude.subNat))) ((fun (x : ((@SAWCoreScaffolding.Nat))) => ((@TCNum) (0)))) ((fun (y : ((@SAWCoreScaffolding.Nat))) => ((@TCInf)))) (((@TCNum) (0)))).

Definition tcMul : (((@Num))) -> (((@Num))) -> ((@Num)) :=
  ((@binaryNumFun) (((@SAWCorePrelude.mulNat))) ((fun (x : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.if0Nat) (((@Num))) (x) (((@TCNum) (0))) (((@TCInf)))))) ((fun (y : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.if0Nat) (((@Num))) (y) (((@TCNum) (0))) (((@TCInf)))))) (((@TCInf)))).

Definition tcDiv : (((@Num))) -> (((@Num))) -> ((@Num)) :=
  ((@binaryNumFun) ((fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.divNat) (x) (y)))) ((fun (x : ((@SAWCoreScaffolding.Nat))) => ((@TCNum) (0)))) ((fun (y : ((@SAWCoreScaffolding.Nat))) => ((@TCInf)))) (((@TCNum) (1)))).

Definition tcMod : (((@Num))) -> (((@Num))) -> ((@Num)) :=
  ((@binaryNumFun) ((fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.modNat) (x) (y)))) ((fun (x : ((@SAWCoreScaffolding.Nat))) => ((@TCNum) (0)))) ((fun (y : ((@SAWCoreScaffolding.Nat))) => ((@TCNum) (0)))) (((@TCNum) (0)))).

Definition tcExp : (((@Num))) -> (((@Num))) -> ((@Num)) :=
  ((@binaryNumFun) (((@SAWCorePrelude.expNat))) ((fun (x : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.natCase) ((fun (_ : ((@SAWCoreScaffolding.Nat))) => ((@Num)))) (((@TCNum) (0))) ((fun (x_minus_1 : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.if0Nat) (((@Num))) (x_minus_1) (((@TCNum) (1))) (((@TCInf)))))) (x)))) ((fun (y : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.if0Nat) (((@Num))) (y) (((@TCNum) (1))) (((@TCInf)))))) (((@TCInf)))).

Definition tcMin : (((@Num))) -> (((@Num))) -> ((@Num)) :=
  ((@binaryNumFun) (((@SAWCorePrelude.minNat))) ((fun (x : ((@SAWCoreScaffolding.Nat))) => ((@TCNum) (x)))) ((fun (y : ((@SAWCoreScaffolding.Nat))) => ((@TCNum) (y)))) (((@TCInf)))).

Definition tcMax : (((@Num))) -> (((@Num))) -> ((@Num)) :=
  ((@binaryNumFun) (((@SAWCorePrelude.maxNat))) ((fun (x : ((@SAWCoreScaffolding.Nat))) => ((@TCInf)))) ((fun (y : ((@SAWCoreScaffolding.Nat))) => ((@TCInf)))) (((@TCInf)))).

Definition ceilDivNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.divNat) (((@SAWCorePrelude.addNat) (x) (((@SAWCorePrelude.subNat) (y) (1))))) (y))).

Definition ceilModNat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.subNat) (((@SAWCorePrelude.mulNat) (((@ceilDivNat) (x) (y))) (y))) (x))).

Definition tcCeilDiv : (((@Num))) -> (((@Num))) -> ((@Num)) :=
  ((@binaryNumFun) (((@ceilDivNat))) ((fun (x : ((@SAWCoreScaffolding.Nat))) => ((@TCNum) (0)))) ((fun (y : ((@SAWCoreScaffolding.Nat))) => ((@TCInf)))) (((@TCInf)))).

Definition tcCeilMod : (((@Num))) -> (((@Num))) -> ((@Num)) :=
  ((@binaryNumFun) (((@ceilModNat))) ((fun (x : ((@SAWCoreScaffolding.Nat))) => ((@TCNum) (0)))) ((fun (y : ((@SAWCoreScaffolding.Nat))) => ((@TCInf)))) (((@TCInf)))).

Definition tcLenFromThenTo_Nat : (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> (((@SAWCoreScaffolding.Nat))) -> ((@SAWCoreScaffolding.Nat)) :=
  (fun (x : ((@SAWCoreScaffolding.Nat))) (y : ((@SAWCoreScaffolding.Nat))) (z : ((@SAWCoreScaffolding.Nat))) => if ((@SAWCorePrelude.ltNat) (x) (y)) then if ((@SAWCorePrelude.ltNat) (z) (x)) then 0 else ((@SAWCorePrelude.addNat) (((@SAWCorePrelude.divNat) (((@SAWCorePrelude.subNat) (z) (x))) (((@SAWCorePrelude.subNat) (y) (x))))) (1)) else if ((@SAWCorePrelude.ltNat) (x) (z)) then 0 else ((@SAWCorePrelude.addNat) (((@SAWCorePrelude.divNat) (((@SAWCorePrelude.subNat) (x) (z))) (((@SAWCorePrelude.subNat) (x) (y))))) (1))).

Definition tcLenFromThenTo : (((@Num))) -> (((@Num))) -> (((@Num))) -> ((@Num)) :=
  ((@ternaryNumFun) (((@tcLenFromThenTo_Nat))) (((@TCInf)))).

Definition seq : (((@Num))) -> (Type) -> Type :=
  (fun (num : ((@Num))) (a : Type) => ((CryptolPrimitives.Num_rect) ((fun (num : ((@Num))) => Type)) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) (((@SAWCorePrelude.Stream) (a))) (num))).

Definition seq_TCNum : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), ((@SAWCoreScaffolding.Eq) (Type) (((@seq) (((@TCNum) (n))) (a))) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) => ((@SAWCoreScaffolding.Refl) (Type) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))).

Definition seq_TCInf : forall (a : Type), ((@SAWCoreScaffolding.Eq) (Type) (((@seq) (((@TCInf))) (a))) (((@SAWCorePrelude.Stream) (a)))) :=
  (fun (a : Type) => ((@SAWCoreScaffolding.Refl) (Type) (((@SAWCorePrelude.Stream) (a))))).

Definition seqMap : forall (a : Type), forall (b : Type), forall (n : ((@Num))), ((a) -> b) -> (((@seq) (n) (a))) -> ((@seq) (n) (b)) :=
  (fun (a : Type) (b : Type) (num : ((@Num))) (f : (a) -> b) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (((@seq) (n) (a))) -> ((@seq) (n) (b)))) (((@SAWCorePrelude.map) (a) (b) (f))) (((@SAWCorePrelude.streamMap) (a) (b) (f))) (num))).

Definition seqConst : forall (n : ((@Num))), forall (a : Type), (a) -> ((@seq) (n) (a)) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => forall (a : Type), (a) -> ((@seq) (n) (a)))) (((@SAWCorePrelude.replicate))) (((@SAWCorePrelude.streamConst))) (n))).

Definition IntModNum : forall (num : ((@Num))), Type :=
  (fun (num : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => Type)) (((@SAWCoreScaffolding.IntMod))) (((@SAWCoreScaffolding.Integer))) (num))).

Definition seq_cong : forall (m : ((@Num))), forall (n : ((@Num))), forall (a : Type), forall (b : Type), (((@SAWCoreScaffolding.Eq) (((@Num))) (m) (n))) -> (((@SAWCoreScaffolding.Eq) (Type) (a) (b))) -> ((@SAWCoreScaffolding.Eq) (Type) (((@seq) (m) (a))) (((@seq) (n) (b)))) :=
  (fun (m : ((@Num))) (n : ((@Num))) (a : Type) (b : Type) (eq_mn : ((@SAWCoreScaffolding.Eq) (((@Num))) (m) (n))) (eq_ab : ((@SAWCoreScaffolding.Eq) (Type) (a) (b))) => ((@SAWCorePrelude.trans) (Type) (((@seq) (m) (a))) (((@seq) (n) (a))) (((@seq) (n) (b))) (((@SAWCorePrelude.eq_cong) (((@Num))) (m) (n) (eq_mn) (Type) ((fun (x : ((@Num))) => ((@seq) (x) (a)))))) (((@SAWCorePrelude.eq_cong) (Type) (a) (b) (eq_ab) (Type) ((fun (x : Type) => ((@seq) (n) (x)))))))).

Definition seq_cong1 : forall (m : ((@Num))), forall (n : ((@Num))), forall (a : Type), (((@SAWCoreScaffolding.Eq) (((@Num))) (m) (n))) -> ((@SAWCoreScaffolding.Eq) (Type) (((@seq) (m) (a))) (((@seq) (n) (a)))) :=
  (fun (m : ((@Num))) (n : ((@Num))) (a : Type) (eq_mn : ((@SAWCoreScaffolding.Eq) (((@Num))) (m) (n))) => ((@SAWCorePrelude.eq_cong) (((@Num))) (m) (n) (eq_mn) (Type) ((fun (x : ((@Num))) => ((@seq) (x) (a)))))).

Definition fun_cong : forall (a : Type), forall (b : Type), forall (c : Type), forall (d : Type), (((@SAWCoreScaffolding.Eq) (Type) (a) (b))) -> (((@SAWCoreScaffolding.Eq) (Type) (c) (d))) -> ((@SAWCoreScaffolding.Eq) (Type) ((a) -> c) ((b) -> d)) :=
  (fun (a : Type) (b : Type) (c : Type) (d : Type) (eq_ab : ((@SAWCoreScaffolding.Eq) (Type) (a) (b))) (eq_cd : ((@SAWCoreScaffolding.Eq) (Type) (c) (d))) => ((@SAWCorePrelude.trans) (Type) ((a) -> c) ((b) -> c) ((b) -> d) (((@SAWCorePrelude.eq_cong) (Type) (a) (b) (eq_ab) (Type) ((fun (x : Type) => (x) -> c)))) (((@SAWCorePrelude.eq_cong) (Type) (c) (d) (eq_cd) (Type) ((fun (x : Type) => (b) -> x)))))).

Definition pair_cong : forall (a : Type), forall (a' : Type), forall (b : Type), forall (b' : Type), (((@SAWCoreScaffolding.Eq) (Type) (a) (a'))) -> (((@SAWCoreScaffolding.Eq) (Type) (b) (b'))) -> ((@SAWCoreScaffolding.Eq) (Type) (((prod) (a) (b))) (((prod) (a') (b')))) :=
  (fun (a : Type) (a' : Type) (b : Type) (b' : Type) (eq_a : ((@SAWCoreScaffolding.Eq) (Type) (a) (a'))) (eq_b : ((@SAWCoreScaffolding.Eq) (Type) (b) (b'))) => ((@SAWCorePrelude.trans) (Type) (((prod) (a) (b))) (((prod) (a') (b))) (((prod) (a') (b'))) (((@SAWCorePrelude.eq_cong) (Type) (a) (a') (eq_a) (Type) ((fun (x : Type) => ((prod) (x) (b)))))) (((@SAWCorePrelude.eq_cong) (Type) (b) (b') (eq_b) (Type) ((fun (x : Type) => ((prod) (a') (x)))))))).

Definition pair_cong1 : forall (a : Type), forall (a' : Type), forall (b : Type), (((@SAWCoreScaffolding.Eq) (Type) (a) (a'))) -> ((@SAWCoreScaffolding.Eq) (Type) (((prod) (a) (b))) (((prod) (a') (b)))) :=
  (fun (a : Type) (a' : Type) (b : Type) (eq_a : ((@SAWCoreScaffolding.Eq) (Type) (a) (a'))) => ((@SAWCorePrelude.eq_cong) (Type) (a) (a') (eq_a) (Type) ((fun (x : Type) => ((prod) (x) (b)))))).

Definition pair_cong2 : forall (a : Type), forall (b : Type), forall (b' : Type), (((@SAWCoreScaffolding.Eq) (Type) (b) (b'))) -> ((@SAWCoreScaffolding.Eq) (Type) (((prod) (a) (b))) (((prod) (a) (b')))) :=
  (fun (a : Type) (b : Type) (b' : Type) (eq_b : ((@SAWCoreScaffolding.Eq) (Type) (b) (b'))) => ((@SAWCorePrelude.eq_cong) (Type) (b) (b') (eq_b) (Type) ((fun (x : Type) => ((prod) (a) (x)))))).

(* Cryptol.unsafeAssert_same_Num was skipped *)

Definition eListSel : forall (a : Type), forall (n : ((@Num))), (((@seq) (n) (a))) -> (((@SAWCoreScaffolding.Nat))) -> a :=
  (fun (a : Type) (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (num : ((@Num))) => (((@seq) (num) (a))) -> (((@SAWCoreScaffolding.Nat))) -> a)) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.sawAt) (n) (a)))) (((@SAWCorePrelude.streamGet) (a))) (n))).

Definition from : forall (a : Type), forall (b : Type), forall (m : ((@Num))), forall (n : ((@Num))), (((@seq) (m) (a))) -> ((a) -> ((@seq) (n) (b))) -> ((@seq) (((@tcMul) (m) (n))) (((prod) (a) (b)))) :=
  (fun (a : Type) (b : Type) (m : ((@Num))) (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (m : ((@Num))) => (((@seq) (m) (a))) -> ((a) -> ((@seq) (n) (b))) -> ((@seq) (((@tcMul) (m) (n))) (((prod) (a) (b)))))) ((fun (m : ((@SAWCoreScaffolding.Nat))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) -> ((a) -> ((@seq) (n) (b))) -> ((@seq) (((@tcMul) (((@TCNum) (m))) (n))) (((prod) (a) (b)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) (k : (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (b))) => ((@SAWCorePrelude.join) (m) (n) (((prod) (a) (b))) (((@SAWCorePrelude.map) (a) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((prod) (a) (b))))) ((fun (x : a) => ((@SAWCorePrelude.map) (b) (((prod) (a) (b))) ((fun (y : b) => ((pair) (x) (y)))) (n) (((k) (x)))))) (m) (xs)))))) (((@SAWCorePrelude.natCase) ((fun (m' : ((@SAWCoreScaffolding.Nat))) => (((@SAWCoreVectorsAsCoqVectors.Vec) (m') (a))) -> ((a) -> ((@SAWCorePrelude.Stream) (b))) -> ((@seq) (((@SAWCorePrelude.if0Nat) (((@Num))) (m') (((@TCNum) (0))) (((@TCInf))))) (((prod) (a) (b)))))) ((fun (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (0) (a))) (k : (a) -> ((@SAWCorePrelude.Stream) (b))) => ((@SAWCoreVectorsAsCoqVectors.EmptyVec) (((prod) (a) (b)))))) ((fun (m' : ((@SAWCoreScaffolding.Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (m'))) (a))) (k : (a) -> ((@SAWCorePrelude.Stream) (b))) => (((fun (x : a) => ((@SAWCorePrelude.streamMap) (b) (((prod) (a) (b))) ((fun (y : b) => ((pair) (x) (y)))) (((k) (x)))))) (((@SAWCorePrelude.sawAt) (((@SAWCoreScaffolding.Succ) (m'))) (a) (xs) (0)))))) (m))) (n)))) (((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (((@SAWCorePrelude.Stream) (a))) -> ((a) -> ((@seq) (n) (b))) -> ((@seq) (((@tcMul) (((@TCInf))) (n))) (((prod) (a) (b)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.natCase) ((fun (n' : ((@SAWCoreScaffolding.Nat))) => (((@SAWCorePrelude.Stream) (a))) -> ((a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n') (b))) -> ((@seq) (((@SAWCorePrelude.if0Nat) (((@Num))) (n') (((@TCNum) (0))) (((@TCInf))))) (((prod) (a) (b)))))) ((fun (xs : ((@SAWCorePrelude.Stream) (a))) (k : (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (0) (b))) => ((@SAWCoreVectorsAsCoqVectors.EmptyVec) (((prod) (a) (b)))))) ((fun (n' : ((@SAWCoreScaffolding.Nat))) (xs : ((@SAWCorePrelude.Stream) (a))) (k : (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n'))) (b))) => ((@SAWCorePrelude.streamJoin) (((prod) (a) (b))) (n') (((@SAWCorePrelude.streamMap) (a) (((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n'))) (((prod) (a) (b))))) ((fun (x : a) => ((@SAWCorePrelude.map) (b) (((prod) (a) (b))) ((fun (y : b) => ((pair) (x) (y)))) (((@SAWCoreScaffolding.Succ) (n'))) (((k) (x)))))) (xs)))))) (n)))) ((fun (xs : ((@SAWCorePrelude.Stream) (a))) (k : (a) -> ((@SAWCorePrelude.Stream) (b))) => (((fun (x : a) => ((@SAWCorePrelude.streamMap) (b) (((prod) (a) (b))) ((fun (y : b) => ((pair) (x) (y)))) (((k) (x)))))) (((@SAWCorePrelude.streamGet) (a) (xs) (0)))))) (n))) (m))).

Definition mlet : forall (a : Type), forall (b : Type), forall (n : ((@Num))), (a) -> ((a) -> ((@seq) (n) (b))) -> ((@seq) (n) (((prod) (a) (b)))) :=
  (fun (a : Type) (b : Type) (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (a) -> ((a) -> ((@seq) (n) (b))) -> ((@seq) (n) (((prod) (a) (b)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (x : a) (f : (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (b))) => ((@SAWCorePrelude.map) (b) (((prod) (a) (b))) ((fun (y : b) => ((pair) (x) (y)))) (n) (((f) (x)))))) ((fun (x : a) (f : (a) -> ((@SAWCorePrelude.Stream) (b))) => ((@SAWCorePrelude.streamMap) (b) (((prod) (a) (b))) ((fun (y : b) => ((pair) (x) (y)))) (((f) (x)))))) (n))).

Definition seqZip : forall (a : Type), forall (b : Type), forall (m : ((@Num))), forall (n : ((@Num))), (((@seq) (m) (a))) -> (((@seq) (n) (b))) -> ((@seq) (((@tcMin) (m) (n))) (((prod) (a) (b)))) :=
  (fun (a : Type) (b : Type) (m : ((@Num))) (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (m : ((@Num))) => (((@seq) (m) (a))) -> (((@seq) (n) (b))) -> ((@seq) (((@tcMin) (m) (n))) (((prod) (a) (b)))))) ((fun (m : ((@SAWCoreScaffolding.Nat))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) -> (((@seq) (n) (b))) -> ((@seq) (((@tcMin) (((@TCNum) (m))) (n))) (((prod) (a) (b)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.zip) (a) (b) (m) (n)))) ((fun (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) (ys : ((@SAWCorePrelude.Stream) (b))) => ((@SAWCoreVectorsAsCoqVectors.gen) (m) (((prod) (a) (b))) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((pair) (((@SAWCorePrelude.sawAt) (m) (a) (xs) (i))) (((@SAWCorePrelude.streamGet) (b) (ys) (i))))))))) (n)))) (((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (((@SAWCorePrelude.Stream) (a))) -> (((@seq) (n) (b))) -> ((@seq) (((@tcMin) (((@TCInf))) (n))) (((prod) (a) (b)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (xs : ((@SAWCorePrelude.Stream) (a))) (ys : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (b))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (((prod) (a) (b))) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((pair) (((@SAWCorePrelude.streamGet) (a) (xs) (i))) (((@SAWCorePrelude.sawAt) (n) (b) (ys) (i))))))))) (((@SAWCorePrelude.streamMap2) (a) (b) (((prod) (a) (b))) ((fun (x : a) (y : b) => ((pair) (x) (y)))))) (n))) (m))).

Definition seqBinary : forall (n : ((@Num))), forall (a : Type), ((a) -> (a) -> a) -> (((@seq) (n) (a))) -> (((@seq) (n) (a))) -> ((@seq) (n) (a)) :=
  (fun (num : ((@Num))) (a : Type) (f : (a) -> (a) -> a) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (((@seq) (n) (a))) -> (((@seq) (n) (a))) -> ((@seq) (n) (a)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.zipWith) (a) (a) (a) (f) (n)))) (((@SAWCorePrelude.streamMap2) (a) (a) (a) (f))) (num))).

Definition unitUnary : (unit) -> unit :=
  (fun (_ : unit) => tt).

Definition unitBinary : (unit) -> (unit) -> unit :=
  (fun (_ : unit) (_ : unit) => tt).

Definition pairUnary : forall (a : Type), forall (b : Type), ((a) -> a) -> ((b) -> b) -> (((prod) (a) (b))) -> ((prod) (a) (b)) :=
  (fun (a : Type) (b : Type) (f : (a) -> a) (g : (b) -> b) (xy : ((prod) (a) (b))) => ((pair) (((f) (((@SAWCoreScaffolding.fst) (a) (b) (xy))))) (((g) (((@SAWCoreScaffolding.snd) (a) (b) (xy))))))).

Definition pairBinary : forall (a : Type), forall (b : Type), ((a) -> (a) -> a) -> ((b) -> (b) -> b) -> (((prod) (a) (b))) -> (((prod) (a) (b))) -> ((prod) (a) (b)) :=
  (fun (a : Type) (b : Type) (f : (a) -> (a) -> a) (g : (b) -> (b) -> b) (x12 : ((prod) (a) (b))) (y12 : ((prod) (a) (b))) => ((pair) (((f) (((@SAWCoreScaffolding.fst) (a) (b) (x12))) (((@SAWCoreScaffolding.fst) (a) (b) (y12))))) (((g) (((@SAWCoreScaffolding.snd) (a) (b) (x12))) (((@SAWCoreScaffolding.snd) (a) (b) (y12))))))).

Definition funBinary : forall (a : Type), forall (b : Type), ((b) -> (b) -> b) -> ((a) -> b) -> ((a) -> b) -> (a) -> b :=
  (fun (a : Type) (b : Type) (op : (b) -> (b) -> b) (f : (a) -> b) (g : (a) -> b) (x : a) => ((op) (((f) (x))) (((g) (x))))).

Definition errorUnary : forall (s : ((@SAWCoreScaffolding.String))), forall (a : Type), (a) -> a :=
  (fun (s : ((@SAWCoreScaffolding.String))) (a : Type) (_ : a) => ((@SAWCoreScaffolding.error) (a) (s))).

Definition errorBinary : forall (s : ((@SAWCoreScaffolding.String))), forall (a : Type), (a) -> (a) -> a :=
  (fun (s : ((@SAWCoreScaffolding.String))) (a : Type) (_ : a) (_ : a) => ((@SAWCoreScaffolding.error) (a) (s))).

Definition boolCmp : (((@SAWCoreScaffolding.Bool))) -> (((@SAWCoreScaffolding.Bool))) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (x : ((@SAWCoreScaffolding.Bool))) (y : ((@SAWCoreScaffolding.Bool))) (k : ((@SAWCoreScaffolding.Bool))) => if x then ((@SAWCoreScaffolding.and) (y) (k)) else ((@SAWCoreScaffolding.or) (y) (k))).

Definition integerCmp : (((@SAWCoreScaffolding.Integer))) -> (((@SAWCoreScaffolding.Integer))) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (x : ((@SAWCoreScaffolding.Integer))) (y : ((@SAWCoreScaffolding.Integer))) (k : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.or) (((@SAWCoreScaffolding.intLt) (x) (y))) (((@SAWCoreScaffolding.and) (((@SAWCoreScaffolding.intEq) (x) (y))) (k))))).

Definition bvCmp : forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (k : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.or) (((@SAWCoreVectorsAsCoqVectors.bvult) (n) (x) (y))) (((@SAWCoreScaffolding.and) (((@SAWCorePrelude.bvEq) (n) (x) (y))) (k))))).

Definition bvSCmp : forall (n : ((@SAWCoreScaffolding.Nat))), (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCorePrelude.bitvector) (n))) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (y : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) (k : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.or) (((@SAWCoreVectorsAsCoqVectors.bvslt) (n) (x) (y))) (((@SAWCoreScaffolding.and) (((@SAWCorePrelude.bvEq) (n) (x) (y))) (k))))).

Definition vecCmp : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (f : (a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (ys : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (k : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreVectorsAsCoqVectors.foldr) ((((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.Bool))) (n) ((fun (f : (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) => f)) (k) (((@SAWCorePrelude.zipWith) (a) (a) ((((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (f) (n) (xs) (ys))))).

Definition unitCmp : (unit) -> (unit) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (_ : unit) (_ : unit) (_ : ((@SAWCoreScaffolding.Bool))) => ((@SAWCoreScaffolding.false))).

Definition pairEq : forall (a : Type), forall (b : Type), ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) -> ((b) -> (b) -> ((@SAWCoreScaffolding.Bool))) -> (((prod) (a) (b))) -> (((prod) (a) (b))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (a : Type) (b : Type) (f : (a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (g : (b) -> (b) -> ((@SAWCoreScaffolding.Bool))) (x : ((prod) (a) (b))) (y : ((prod) (a) (b))) => ((@SAWCoreScaffolding.and) (((f) (((@SAWCoreScaffolding.fst) (a) (b) (x))) (((@SAWCoreScaffolding.fst) (a) (b) (y))))) (((g) (((@SAWCoreScaffolding.snd) (a) (b) (x))) (((@SAWCoreScaffolding.snd) (a) (b) (y))))))).

Definition pairCmp : forall (a : Type), forall (b : Type), ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) -> ((b) -> (b) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) -> (((prod) (a) (b))) -> (((prod) (a) (b))) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (a : Type) (b : Type) (f : (a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (g : (b) -> (b) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (x12 : ((prod) (a) (b))) (y12 : ((prod) (a) (b))) (k : ((@SAWCoreScaffolding.Bool))) => ((f) (((@SAWCoreScaffolding.fst) (a) (b) (x12))) (((@SAWCoreScaffolding.fst) (a) (b) (y12))) (((g) (((@SAWCoreScaffolding.snd) (a) (b) (x12))) (((@SAWCoreScaffolding.snd) (a) (b) (y12))) (k))))).

Definition PZero : (Type) -> Type :=
  (fun (a : Type) => a).

Definition PZeroBit : ((@PZero) (((@SAWCoreScaffolding.Bool)))) :=
  ((@SAWCoreScaffolding.false)).

Definition PZeroInteger : ((@PZero) (((@SAWCoreScaffolding.Integer)))) :=
  ((@SAWCoreScaffolding.natToInt) (0)).

Definition PZeroIntMod : forall (n : ((@SAWCoreScaffolding.Nat))), ((@PZero) (((@SAWCoreScaffolding.IntMod) (n)))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.toIntMod) (n) (((@SAWCoreScaffolding.natToInt) (0))))).

Definition PZeroIntModNum : forall (num : ((@Num))), ((@PZero) (((@IntModNum) (num)))) :=
  (fun (num : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => ((@PZero) (((@IntModNum) (n)))))) (((@PZeroIntMod))) (((@PZeroInteger))) (num))).

Definition PZeroSeq : forall (n : ((@Num))), forall (a : Type), (((@PZero) (a))) -> ((@PZero) (((@seq) (n) (a)))) :=
  (fun (n : ((@Num))) (a : Type) (pa : a) => ((@seqConst) (n) (a) (pa))).

Definition PZeroSeqBool : forall (n : ((@Num))), ((@PZero) (((@seq) (n) (((@SAWCoreScaffolding.Bool)))))) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => ((@PZero) (((@seq) (n) (((@SAWCoreScaffolding.Bool)))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (0)))) (((@SAWCorePrelude.streamConst) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))))) (n))).

Definition PZeroFun : forall (a : Type), forall (b : Type), (((@PZero) (b))) -> ((@PZero) ((a) -> b)) :=
  (fun (a : Type) (b : Type) (pb : b) (_ : a) => pb).

Definition PLogic : (Type) -> Type :=
  (fun (a : Type) => ((RecordTypeCons) ("and") ((a) -> (a) -> a) (((RecordTypeCons) ("or") ((a) -> (a) -> a) (((RecordTypeCons) ("xor") ((a) -> (a) -> a) (((RecordTypeCons) ("not") ((a) -> a) (RecordTypeNil))))))))).

Definition PLogicBit : ((@PLogic) (((@SAWCoreScaffolding.Bool)))) :=
  ((RecordCons) ("and") (((@SAWCoreScaffolding.and))) (((RecordCons) ("or") (((@SAWCoreScaffolding.or))) (((RecordCons) ("xor") (((@SAWCoreScaffolding.xor))) (((RecordCons) ("not") (((@SAWCoreScaffolding.not))) (RecordNil)))))))).

Definition PLogicVec : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@PLogic) (a))) -> ((@PLogic) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (pa : ((RecordTypeCons) ("and") ((a) -> (a) -> a) (((RecordTypeCons) ("not") ((a) -> a) (((RecordTypeCons) ("or") ((a) -> (a) -> a) (((RecordTypeCons) ("xor") ((a) -> (a) -> a) (RecordTypeNil))))))))) => ((RecordCons) ("and") (((@SAWCorePrelude.zipWith) (a) (a) (a) (((RecordProj) (pa) ("and"))) (n))) (((RecordCons) ("or") (((@SAWCorePrelude.zipWith) (a) (a) (a) (((RecordProj) (pa) ("or"))) (n))) (((RecordCons) ("xor") (((@SAWCorePrelude.zipWith) (a) (a) (a) (((RecordProj) (pa) ("xor"))) (n))) (((RecordCons) ("not") (((@SAWCorePrelude.map) (a) (a) (((RecordProj) (pa) ("not"))) (n))) (RecordNil))))))))).

Definition PLogicStream : forall (a : Type), (((@PLogic) (a))) -> ((@PLogic) (((@SAWCorePrelude.Stream) (a)))) :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("and") ((a) -> (a) -> a) (((RecordTypeCons) ("not") ((a) -> a) (((RecordTypeCons) ("or") ((a) -> (a) -> a) (((RecordTypeCons) ("xor") ((a) -> (a) -> a) (RecordTypeNil))))))))) => ((RecordCons) ("and") (((@SAWCorePrelude.streamMap2) (a) (a) (a) (((RecordProj) (pa) ("and"))))) (((RecordCons) ("or") (((@SAWCorePrelude.streamMap2) (a) (a) (a) (((RecordProj) (pa) ("or"))))) (((RecordCons) ("xor") (((@SAWCorePrelude.streamMap2) (a) (a) (a) (((RecordProj) (pa) ("xor"))))) (((RecordCons) ("not") (((@SAWCorePrelude.streamMap) (a) (a) (((RecordProj) (pa) ("not"))))) (RecordNil))))))))).

Definition PLogicSeq : forall (n : ((@Num))), forall (a : Type), (((@PLogic) (a))) -> ((@PLogic) (((@seq) (n) (a)))) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => forall (a : Type), (((@PLogic) (a))) -> ((@PLogic) (((@seq) (n) (a)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@PLogicVec) (n)))) (((@PLogicStream))) (n))).

Definition PLogicWord : forall (n : ((@SAWCoreScaffolding.Nat))), ((@PLogic) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool)))))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) => ((RecordCons) ("and") (((@SAWCorePrelude.bvAnd) (n))) (((RecordCons) ("or") (((@SAWCorePrelude.bvOr) (n))) (((RecordCons) ("xor") (((@SAWCorePrelude.bvXor) (n))) (((RecordCons) ("not") (((@SAWCorePrelude.bvNot) (n))) (RecordNil))))))))).

Definition PLogicSeqBool : forall (n : ((@Num))), ((@PLogic) (((@seq) (n) (((@SAWCoreScaffolding.Bool)))))) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => ((@PLogic) (((@seq) (n) (((@SAWCoreScaffolding.Bool)))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@PLogicWord) (n)))) (((@PLogicStream) (((@SAWCoreScaffolding.Bool))) (((@PLogicBit))))) (n))).

Definition PLogicFun : forall (a : Type), forall (b : Type), (((@PLogic) (b))) -> ((@PLogic) ((a) -> b)) :=
  (fun (a : Type) (b : Type) (pb : ((RecordTypeCons) ("and") ((b) -> (b) -> b) (((RecordTypeCons) ("not") ((b) -> b) (((RecordTypeCons) ("or") ((b) -> (b) -> b) (((RecordTypeCons) ("xor") ((b) -> (b) -> b) (RecordTypeNil))))))))) => ((RecordCons) ("and") (((@funBinary) (a) (b) (((RecordProj) (pb) ("and"))))) (((RecordCons) ("or") (((@funBinary) (a) (b) (((RecordProj) (pb) ("or"))))) (((RecordCons) ("xor") (((@funBinary) (a) (b) (((RecordProj) (pb) ("xor"))))) (((RecordCons) ("not") (((@compose) (a) (b) (b) (((RecordProj) (pb) ("not"))))) (RecordNil))))))))).

Definition PLogicUnit : ((@PLogic) (unit)) :=
  ((RecordCons) ("and") (((@unitBinary))) (((RecordCons) ("or") (((@unitBinary))) (((RecordCons) ("xor") (((@unitBinary))) (((RecordCons) ("not") (((@unitUnary))) (RecordNil)))))))).

Definition PLogicPair : forall (a : Type), forall (b : Type), (((@PLogic) (a))) -> (((@PLogic) (b))) -> ((@PLogic) (((prod) (a) (b)))) :=
  (fun (a : Type) (b : Type) (pa : ((RecordTypeCons) ("and") ((a) -> (a) -> a) (((RecordTypeCons) ("not") ((a) -> a) (((RecordTypeCons) ("or") ((a) -> (a) -> a) (((RecordTypeCons) ("xor") ((a) -> (a) -> a) (RecordTypeNil))))))))) (pb : ((RecordTypeCons) ("and") ((b) -> (b) -> b) (((RecordTypeCons) ("not") ((b) -> b) (((RecordTypeCons) ("or") ((b) -> (b) -> b) (((RecordTypeCons) ("xor") ((b) -> (b) -> b) (RecordTypeNil))))))))) => ((RecordCons) ("and") (((@pairBinary) (a) (b) (((RecordProj) (pa) ("and"))) (((RecordProj) (pb) ("and"))))) (((RecordCons) ("or") (((@pairBinary) (a) (b) (((RecordProj) (pa) ("or"))) (((RecordProj) (pb) ("or"))))) (((RecordCons) ("xor") (((@pairBinary) (a) (b) (((RecordProj) (pa) ("xor"))) (((RecordProj) (pb) ("xor"))))) (((RecordCons) ("not") (((@pairUnary) (a) (b) (((RecordProj) (pa) ("not"))) (((RecordProj) (pb) ("not"))))) (RecordNil))))))))).

Definition PArith : (Type) -> Type :=
  (fun (a : Type) => ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (RecordTypeNil))))))))))))))))))))))).

Definition PArithInteger : ((@PArith) (((@SAWCoreScaffolding.Integer)))) :=
  ((RecordCons) ("add") (((@SAWCoreScaffolding.intAdd))) (((RecordCons) ("sub") (((@SAWCoreScaffolding.intSub))) (((RecordCons) ("mul") (((@SAWCoreScaffolding.intMul))) (((RecordCons) ("div") (((@SAWCoreScaffolding.intDiv))) (((RecordCons) ("mod") (((@SAWCoreScaffolding.intMod))) (((RecordCons) ("exp") (((@errorBinary) (("no implementation for exp on Integer")%string) (((@SAWCoreScaffolding.Integer))))) (((RecordCons) ("lg2") (((@errorUnary) (("no implementation for lg2 on Integer")%string) (((@SAWCoreScaffolding.Integer))))) (((RecordCons) ("neg") (((@SAWCoreScaffolding.intNeg))) (((RecordCons) ("sdiv") (((@errorBinary) (("no implementation for sdiv on Integer")%string) (((@SAWCoreScaffolding.Integer))))) (((RecordCons) ("smod") (((@errorBinary) (("no implementation for smod on Integer")%string) (((@SAWCoreScaffolding.Integer))))) (((RecordCons) ("int") ((fun (i : ((@SAWCoreScaffolding.Integer))) => i)) (RecordNil)))))))))))))))))))))).

Definition PArithIntMod : forall (n : ((@SAWCoreScaffolding.Nat))), ((@PArith) (((@SAWCoreScaffolding.IntMod) (n)))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) => ((RecordCons) ("add") (((@SAWCoreScaffolding.intModAdd) (n))) (((RecordCons) ("sub") (((@SAWCoreScaffolding.intModSub) (n))) (((RecordCons) ("mul") (((@SAWCoreScaffolding.intModMul) (n))) (((RecordCons) ("div") ((fun (x : ((@SAWCoreScaffolding.IntMod) (n))) (y : ((@SAWCoreScaffolding.IntMod) (n))) => ((@SAWCoreScaffolding.toIntMod) (n) (((@SAWCoreScaffolding.intDiv) (((@SAWCoreScaffolding.fromIntMod) (n) (x))) (((@SAWCoreScaffolding.fromIntMod) (n) (y)))))))) (((RecordCons) ("mod") ((fun (x : ((@SAWCoreScaffolding.IntMod) (n))) (y : ((@SAWCoreScaffolding.IntMod) (n))) => ((@SAWCoreScaffolding.toIntMod) (n) (((@SAWCoreScaffolding.intMod) (((@SAWCoreScaffolding.fromIntMod) (n) (x))) (((@SAWCoreScaffolding.fromIntMod) (n) (y)))))))) (((RecordCons) ("exp") (((@errorBinary) (("no implementation for exp on IntMod")%string) (((@SAWCoreScaffolding.IntMod) (n))))) (((RecordCons) ("lg2") (((@errorUnary) (("no implementation for lg2 on IntMod")%string) (((@SAWCoreScaffolding.IntMod) (n))))) (((RecordCons) ("neg") (((@SAWCoreScaffolding.intModNeg) (n))) (((RecordCons) ("sdiv") (((@errorBinary) (("no implementation for sdiv on IntMod")%string) (((@SAWCoreScaffolding.IntMod) (n))))) (((RecordCons) ("smod") (((@errorBinary) (("no implementation for smod on IntMod")%string) (((@SAWCoreScaffolding.IntMod) (n))))) (((RecordCons) ("int") (((@SAWCoreScaffolding.toIntMod) (n))) (RecordNil))))))))))))))))))))))).

Definition PArithIntModNum : forall (num : ((@Num))), ((@PArith) (((@IntModNum) (num)))) :=
  (fun (num : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => ((@PArith) (((@IntModNum) (n)))))) (((@PArithIntMod))) (((@PArithInteger))) (num))).

Definition PArithVec : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@PArith) (a))) -> ((@PArith) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordCons) ("add") (((@SAWCorePrelude.zipWith) (a) (a) (a) (((RecordProj) (pa) ("add"))) (n))) (((RecordCons) ("sub") (((@SAWCorePrelude.zipWith) (a) (a) (a) (((RecordProj) (pa) ("sub"))) (n))) (((RecordCons) ("mul") (((@SAWCorePrelude.zipWith) (a) (a) (a) (((RecordProj) (pa) ("mul"))) (n))) (((RecordCons) ("div") (((@SAWCorePrelude.zipWith) (a) (a) (a) (((RecordProj) (pa) ("div"))) (n))) (((RecordCons) ("mod") (((@SAWCorePrelude.zipWith) (a) (a) (a) (((RecordProj) (pa) ("mod"))) (n))) (((RecordCons) ("exp") (((@SAWCorePrelude.zipWith) (a) (a) (a) (((RecordProj) (pa) ("exp"))) (n))) (((RecordCons) ("lg2") (((@SAWCorePrelude.map) (a) (a) (((RecordProj) (pa) ("lg2"))) (n))) (((RecordCons) ("neg") (((@SAWCorePrelude.map) (a) (a) (((RecordProj) (pa) ("neg"))) (n))) (((RecordCons) ("sdiv") (((@SAWCorePrelude.zipWith) (a) (a) (a) (((RecordProj) (pa) ("sdiv"))) (n))) (((RecordCons) ("smod") (((@SAWCorePrelude.zipWith) (a) (a) (a) (((RecordProj) (pa) ("smod"))) (n))) (((RecordCons) ("int") ((fun (i : ((@SAWCoreScaffolding.Integer))) => ((@SAWCorePrelude.replicate) (n) (a) (((((RecordProj) (pa) ("int"))) (i)))))) (RecordNil))))))))))))))))))))))).

Definition PArithStream : forall (a : Type), (((@PArith) (a))) -> ((@PArith) (((@SAWCorePrelude.Stream) (a)))) :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordCons) ("add") (((@SAWCorePrelude.streamMap2) (a) (a) (a) (((RecordProj) (pa) ("add"))))) (((RecordCons) ("sub") (((@SAWCorePrelude.streamMap2) (a) (a) (a) (((RecordProj) (pa) ("sub"))))) (((RecordCons) ("mul") (((@SAWCorePrelude.streamMap2) (a) (a) (a) (((RecordProj) (pa) ("mul"))))) (((RecordCons) ("div") (((@SAWCorePrelude.streamMap2) (a) (a) (a) (((RecordProj) (pa) ("div"))))) (((RecordCons) ("mod") (((@SAWCorePrelude.streamMap2) (a) (a) (a) (((RecordProj) (pa) ("mod"))))) (((RecordCons) ("exp") (((@SAWCorePrelude.streamMap2) (a) (a) (a) (((RecordProj) (pa) ("exp"))))) (((RecordCons) ("lg2") (((@SAWCorePrelude.streamMap) (a) (a) (((RecordProj) (pa) ("lg2"))))) (((RecordCons) ("neg") (((@SAWCorePrelude.streamMap) (a) (a) (((RecordProj) (pa) ("neg"))))) (((RecordCons) ("sdiv") (((@SAWCorePrelude.streamMap2) (a) (a) (a) (((RecordProj) (pa) ("sdiv"))))) (((RecordCons) ("smod") (((@SAWCorePrelude.streamMap2) (a) (a) (a) (((RecordProj) (pa) ("smod"))))) (((RecordCons) ("int") ((fun (i : ((@SAWCoreScaffolding.Integer))) => ((@SAWCorePrelude.streamConst) (a) (((((RecordProj) (pa) ("int"))) (i)))))) (RecordNil))))))))))))))))))))))).

Definition PArithSeq : forall (n : ((@Num))), forall (a : Type), (((@PArith) (a))) -> ((@PArith) (((@seq) (n) (a)))) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => forall (a : Type), (((@PArith) (a))) -> ((@PArith) (((@seq) (n) (a)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@PArithVec) (n)))) (((@PArithStream))) (n))).

Definition PArithWord : forall (n : ((@SAWCoreScaffolding.Nat))), ((@PArith) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool)))))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) => ((RecordCons) ("add") (((@SAWCoreVectorsAsCoqVectors.bvAdd) (n))) (((RecordCons) ("sub") (((@SAWCoreVectorsAsCoqVectors.bvSub) (n))) (((RecordCons) ("mul") (((@SAWCoreVectorsAsCoqVectors.bvMul) (n))) (((RecordCons) ("div") (((@SAWCoreVectorsAsCoqVectors.bvUDiv) (n))) (((RecordCons) ("mod") (((@SAWCoreVectorsAsCoqVectors.bvURem) (n))) (((RecordCons) ("exp") (((@bvExp) (n))) (((RecordCons) ("lg2") (((@SAWCoreVectorsAsCoqVectors.bvLg2) (n))) (((RecordCons) ("neg") (((@SAWCoreVectorsAsCoqVectors.bvNeg) (n))) (((RecordCons) ("sdiv") (((@SAWCorePrelude.natCase) ((fun (w : ((@SAWCoreScaffolding.Nat))) => (((@SAWCorePrelude.bitvector) (w))) -> (((@SAWCorePrelude.bitvector) (w))) -> ((@SAWCorePrelude.bitvector) (w)))) (((@errorBinary) (("no implementation for sdiv on empty bit vectors")%string) (((@SAWCorePrelude.bitvector) (0))))) (((@SAWCoreVectorsAsCoqVectors.bvSDiv))) (n))) (((RecordCons) ("smod") (((@SAWCorePrelude.natCase) ((fun (w : ((@SAWCoreScaffolding.Nat))) => (((@SAWCorePrelude.bitvector) (w))) -> (((@SAWCorePrelude.bitvector) (w))) -> ((@SAWCorePrelude.bitvector) (w)))) (((@errorBinary) (("no implementation for smod on empty bit vectors")%string) (((@SAWCorePrelude.bitvector) (0))))) (((@SAWCoreVectorsAsCoqVectors.bvSRem))) (n))) (((RecordCons) ("int") (((@SAWCorePrelude.intToBv) (n))) (RecordNil))))))))))))))))))))))).

Definition PArithSeqBool : forall (n : ((@Num))), ((@PArith) (((@seq) (n) (((@SAWCoreScaffolding.Bool)))))) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => ((@PArith) (((@seq) (n) (((@SAWCoreScaffolding.Bool)))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@PArithWord) (n)))) (((@SAWCoreScaffolding.error) (((@PArith) (((@SAWCorePrelude.Stream) (((@SAWCoreScaffolding.Bool))))))) (("PArithSeqBool: no instance for streams")%string))) (n))).

Definition PArithFun : forall (a : Type), forall (b : Type), (((@PArith) (b))) -> ((@PArith) ((a) -> b)) :=
  (fun (a : Type) (b : Type) (pb : ((RecordTypeCons) ("add") ((b) -> (b) -> b) (((RecordTypeCons) ("div") ((b) -> (b) -> b) (((RecordTypeCons) ("exp") ((b) -> (b) -> b) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> b) (((RecordTypeCons) ("lg2") ((b) -> b) (((RecordTypeCons) ("mod") ((b) -> (b) -> b) (((RecordTypeCons) ("mul") ((b) -> (b) -> b) (((RecordTypeCons) ("neg") ((b) -> b) (((RecordTypeCons) ("sdiv") ((b) -> (b) -> b) (((RecordTypeCons) ("smod") ((b) -> (b) -> b) (((RecordTypeCons) ("sub") ((b) -> (b) -> b) (RecordTypeNil))))))))))))))))))))))) => ((RecordCons) ("add") (((@funBinary) (a) (b) (((RecordProj) (pb) ("add"))))) (((RecordCons) ("sub") (((@funBinary) (a) (b) (((RecordProj) (pb) ("sub"))))) (((RecordCons) ("mul") (((@funBinary) (a) (b) (((RecordProj) (pb) ("mul"))))) (((RecordCons) ("div") (((@funBinary) (a) (b) (((RecordProj) (pb) ("div"))))) (((RecordCons) ("mod") (((@funBinary) (a) (b) (((RecordProj) (pb) ("mod"))))) (((RecordCons) ("exp") (((@funBinary) (a) (b) (((RecordProj) (pb) ("exp"))))) (((RecordCons) ("lg2") (((@compose) (a) (b) (b) (((RecordProj) (pb) ("lg2"))))) (((RecordCons) ("neg") (((@compose) (a) (b) (b) (((RecordProj) (pb) ("neg"))))) (((RecordCons) ("sdiv") (((@funBinary) (a) (b) (((RecordProj) (pb) ("sdiv"))))) (((RecordCons) ("smod") (((@funBinary) (a) (b) (((RecordProj) (pb) ("smod"))))) (((RecordCons) ("int") ((fun (i : ((@SAWCoreScaffolding.Integer))) (_ : a) => ((((RecordProj) (pb) ("int"))) (i)))) (RecordNil))))))))))))))))))))))).

Definition PArithUnit : ((@PArith) (unit)) :=
  ((RecordCons) ("add") (((@unitBinary))) (((RecordCons) ("sub") (((@unitBinary))) (((RecordCons) ("mul") (((@unitBinary))) (((RecordCons) ("div") (((@unitBinary))) (((RecordCons) ("mod") (((@unitBinary))) (((RecordCons) ("exp") (((@unitBinary))) (((RecordCons) ("lg2") (((@unitUnary))) (((RecordCons) ("neg") (((@unitUnary))) (((RecordCons) ("sdiv") (((@unitBinary))) (((RecordCons) ("smod") (((@unitBinary))) (((RecordCons) ("int") ((fun (i : ((@SAWCoreScaffolding.Integer))) => tt)) (RecordNil)))))))))))))))))))))).

Definition PArithPair : forall (a : Type), forall (b : Type), (((@PArith) (a))) -> (((@PArith) (b))) -> ((@PArith) (((prod) (a) (b)))) :=
  (fun (a : Type) (b : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) (pb : ((RecordTypeCons) ("add") ((b) -> (b) -> b) (((RecordTypeCons) ("div") ((b) -> (b) -> b) (((RecordTypeCons) ("exp") ((b) -> (b) -> b) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> b) (((RecordTypeCons) ("lg2") ((b) -> b) (((RecordTypeCons) ("mod") ((b) -> (b) -> b) (((RecordTypeCons) ("mul") ((b) -> (b) -> b) (((RecordTypeCons) ("neg") ((b) -> b) (((RecordTypeCons) ("sdiv") ((b) -> (b) -> b) (((RecordTypeCons) ("smod") ((b) -> (b) -> b) (((RecordTypeCons) ("sub") ((b) -> (b) -> b) (RecordTypeNil))))))))))))))))))))))) => ((RecordCons) ("add") (((@pairBinary) (a) (b) (((RecordProj) (pa) ("add"))) (((RecordProj) (pb) ("add"))))) (((RecordCons) ("sub") (((@pairBinary) (a) (b) (((RecordProj) (pa) ("sub"))) (((RecordProj) (pb) ("sub"))))) (((RecordCons) ("mul") (((@pairBinary) (a) (b) (((RecordProj) (pa) ("mul"))) (((RecordProj) (pb) ("mul"))))) (((RecordCons) ("div") (((@pairBinary) (a) (b) (((RecordProj) (pa) ("div"))) (((RecordProj) (pb) ("div"))))) (((RecordCons) ("mod") (((@pairBinary) (a) (b) (((RecordProj) (pa) ("mod"))) (((RecordProj) (pb) ("mod"))))) (((RecordCons) ("exp") (((@pairBinary) (a) (b) (((RecordProj) (pa) ("exp"))) (((RecordProj) (pb) ("exp"))))) (((RecordCons) ("lg2") (((@pairUnary) (a) (b) (((RecordProj) (pa) ("lg2"))) (((RecordProj) (pb) ("lg2"))))) (((RecordCons) ("neg") (((@pairUnary) (a) (b) (((RecordProj) (pa) ("neg"))) (((RecordProj) (pb) ("neg"))))) (((RecordCons) ("sdiv") (((@pairBinary) (a) (b) (((RecordProj) (pa) ("sdiv"))) (((RecordProj) (pb) ("sdiv"))))) (((RecordCons) ("smod") (((@pairBinary) (a) (b) (((RecordProj) (pa) ("smod"))) (((RecordProj) (pb) ("smod"))))) (((RecordCons) ("int") ((fun (i : ((@SAWCoreScaffolding.Integer))) => ((pair) (((((RecordProj) (pa) ("int"))) (i))) (((((RecordProj) (pb) ("int"))) (i)))))) (RecordNil))))))))))))))))))))))).

Definition PCmp : (Type) -> Type :=
  (fun (a : Type) => ((RecordTypeCons) ("eq") ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (((RecordTypeCons) ("cmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))))).

Definition PCmpBit : ((@PCmp) (((@SAWCoreScaffolding.Bool)))) :=
  ((RecordCons) ("eq") (((@SAWCoreScaffolding.boolEq))) (((RecordCons) ("cmp") (((@boolCmp))) (RecordNil)))).

Definition PCmpInteger : ((@PCmp) (((@SAWCoreScaffolding.Integer)))) :=
  ((RecordCons) ("eq") (((@SAWCoreScaffolding.intEq))) (((RecordCons) ("cmp") (((@integerCmp))) (RecordNil)))).

Definition PCmpIntMod : forall (n : ((@SAWCoreScaffolding.Nat))), ((@PCmp) (((@SAWCoreScaffolding.IntMod) (n)))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) => ((RecordCons) ("eq") (((@SAWCoreScaffolding.intModEq) (n))) (((RecordCons) ("cmp") ((fun (x : ((@SAWCoreScaffolding.IntMod) (n))) (y : ((@SAWCoreScaffolding.IntMod) (n))) => ((@integerCmp) (((@SAWCoreScaffolding.fromIntMod) (n) (x))) (((@SAWCoreScaffolding.fromIntMod) (n) (y)))))) (RecordNil))))).

Definition PCmpIntModNum : forall (num : ((@Num))), ((@PCmp) (((@IntModNum) (num)))) :=
  (fun (num : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => ((@PCmp) (((@IntModNum) (n)))))) (((@PCmpIntMod))) (((@PCmpInteger))) (num))).

Definition PCmpVec : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@PCmp) (a))) -> ((@PCmp) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (pa : ((RecordTypeCons) ("cmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (((RecordTypeCons) ("eq") ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))))) => ((RecordCons) ("eq") (((@SAWCorePrelude.vecEq) (n) (a) (((RecordProj) (pa) ("eq"))))) (((RecordCons) ("cmp") (((@vecCmp) (n) (a) (((RecordProj) (pa) ("cmp"))))) (RecordNil))))).

Definition PCmpSeq : forall (n : ((@Num))), forall (a : Type), (((@PCmp) (a))) -> ((@PCmp) (((@seq) (n) (a)))) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => forall (a : Type), (((@PCmp) (a))) -> ((@PCmp) (((@seq) (n) (a)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@PCmpVec) (n)))) ((fun (a : Type) (pa : ((RecordTypeCons) ("cmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (((RecordTypeCons) ("eq") ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))))) => ((@SAWCoreScaffolding.error) (((@PCmp) (((@SAWCorePrelude.Stream) (a))))) (("invalid Cmp instance")%string)))) (n))).

Definition PCmpWord : forall (n : ((@SAWCoreScaffolding.Nat))), ((@PCmp) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool)))))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) => ((RecordCons) ("eq") (((@SAWCorePrelude.bvEq) (n))) (((RecordCons) ("cmp") (((@bvCmp) (n))) (RecordNil))))).

Definition PCmpSeqBool : forall (n : ((@Num))), ((@PCmp) (((@seq) (n) (((@SAWCoreScaffolding.Bool)))))) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => ((@PCmp) (((@seq) (n) (((@SAWCoreScaffolding.Bool)))))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@PCmpWord) (n)))) (((@SAWCoreScaffolding.error) (((@PCmp) (((@SAWCorePrelude.Stream) (((@SAWCoreScaffolding.Bool))))))) (("invalid Cmp instance")%string))) (n))).

Definition PCmpUnit : ((@PCmp) (unit)) :=
  ((RecordCons) ("eq") ((fun (x : unit) (y : unit) => ((@SAWCoreScaffolding.true)))) (((RecordCons) ("cmp") (((@unitCmp))) (RecordNil)))).

Definition PCmpPair : forall (a : Type), forall (b : Type), (((@PCmp) (a))) -> (((@PCmp) (b))) -> ((@PCmp) (((prod) (a) (b)))) :=
  (fun (a : Type) (b : Type) (pa : ((RecordTypeCons) ("cmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (((RecordTypeCons) ("eq") ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))))) (pb : ((RecordTypeCons) ("cmp") ((b) -> (b) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (((RecordTypeCons) ("eq") ((b) -> (b) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))))) => ((RecordCons) ("eq") (((@pairEq) (a) (b) (((RecordProj) (pa) ("eq"))) (((RecordProj) (pb) ("eq"))))) (((RecordCons) ("cmp") (((@pairCmp) (a) (b) (((RecordProj) (pa) ("cmp"))) (((RecordProj) (pb) ("cmp"))))) (RecordNil))))).

Definition PSignedCmp : (Type) -> Type :=
  (fun (a : Type) => ((RecordTypeCons) ("scmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))).

Definition PSignedCmpVec : forall (n : ((@SAWCoreScaffolding.Nat))), forall (a : Type), (((@PSignedCmp) (a))) -> ((@PSignedCmp) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (pa : ((RecordTypeCons) ("scmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))) => ((RecordCons) ("scmp") (((@vecCmp) (n) (a) (((RecordProj) (pa) ("scmp"))))) (RecordNil))).

Definition PSignedCmpSeq : forall (n : ((@Num))), forall (a : Type), (((@PSignedCmp) (a))) -> ((@PSignedCmp) (((@seq) (n) (a)))) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => forall (a : Type), (((@PSignedCmp) (a))) -> ((@PSignedCmp) (((@seq) (n) (a)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@PSignedCmpVec) (n)))) ((fun (a : Type) (pa : ((RecordTypeCons) ("scmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))) => ((@SAWCoreScaffolding.error) (((@PSignedCmp) (((@SAWCorePrelude.Stream) (a))))) (("invalid SignedCmp instance")%string)))) (n))).

Definition PSignedCmpWord : forall (n : ((@SAWCoreScaffolding.Nat))), ((@PSignedCmp) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool)))))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) => ((RecordCons) ("scmp") (((@bvSCmp) (n))) (RecordNil))).

Definition PSignedCmpUnit : ((@PSignedCmp) (unit)) :=
  ((RecordCons) ("scmp") (((@unitCmp))) (RecordNil)).

Definition PSignedCmpPair : forall (a : Type), forall (b : Type), (((@PSignedCmp) (a))) -> (((@PSignedCmp) (b))) -> ((@PSignedCmp) (((prod) (a) (b)))) :=
  (fun (a : Type) (b : Type) (pa : ((RecordTypeCons) ("scmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))) (pb : ((RecordTypeCons) ("scmp") ((b) -> (b) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))) => ((RecordCons) ("scmp") (((@pairCmp) (a) (b) (((RecordProj) (pa) ("scmp"))) (((RecordProj) (pb) ("scmp"))))) (RecordNil))).

Definition PLiteral : forall (a : Type), Type :=
  (fun (a : Type) => (((@SAWCoreScaffolding.Nat))) -> a).

Definition PLiteralSeqBool : forall (n : ((@Num))), ((@PLiteral) (((@seq) (n) (((@SAWCoreScaffolding.Bool)))))) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => ((@PLiteral) (((@seq) (n) (((@SAWCoreScaffolding.Bool)))))))) (((@SAWCoreVectorsAsCoqVectors.bvNat))) (((@SAWCoreScaffolding.error) (((@PLiteral) (((@SAWCorePrelude.Stream) (((@SAWCoreScaffolding.Bool))))))) (("PLiteralSeqBool: no instance for streams")%string))) (n))).

Definition PLiteralInteger : ((@PLiteral) (((@SAWCoreScaffolding.Integer)))) :=
  ((@SAWCoreScaffolding.natToInt)).

Definition PLiteralIntMod : forall (n : ((@SAWCoreScaffolding.Nat))), ((@PLiteral) (((@SAWCoreScaffolding.IntMod) (n)))) :=
  (fun (n : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreScaffolding.toIntMod) (n) (((@SAWCoreScaffolding.natToInt) (x))))).

Definition PLiteralIntModNum : forall (num : ((@Num))), ((@PLiteral) (((@IntModNum) (num)))) :=
  (fun (num : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => ((@PLiteral) (((@IntModNum) (n)))))) (((@PLiteralIntMod))) (((@PLiteralInteger))) (num))).

Definition ecNumber : forall (val : ((@Num))), forall (a : Type), (((@PLiteral) (a))) -> a :=
  (fun (val : ((@Num))) (a : Type) (pa : (((@SAWCoreScaffolding.Nat))) -> a) => ((CryptolPrimitives.Num_rect) ((fun (_ : ((@Num))) => a)) (pa) (((pa) (0))) (val))).

Definition ecToInteger : forall (n : ((@Num))), (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Integer)) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Integer)))) (((@SAWCorePrelude.bvToInt))) (((@SAWCoreScaffolding.error) ((((@SAWCorePrelude.Stream) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Integer))) (("ecToInteger called on TCInf")%string))) (n))).

Definition ecFromInteger : forall (a : Type), (((@PArith) (a))) -> (((@SAWCoreScaffolding.Integer))) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordProj) (pa) ("int"))).

Definition ecFromZ : forall (n : ((@Num))), (((@IntModNum) (n))) -> ((@SAWCoreScaffolding.Integer)) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (((@IntModNum) (n))) -> ((@SAWCoreScaffolding.Integer)))) (((@SAWCoreScaffolding.fromIntMod))) ((fun (x : ((@SAWCoreScaffolding.Integer))) => x)) (n))).

Definition ecPlus : forall (a : Type), (((@PArith) (a))) -> (a) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordProj) (pa) ("add"))).

Definition ecMinus : forall (a : Type), (((@PArith) (a))) -> (a) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordProj) (pa) ("sub"))).

Definition ecMul : forall (a : Type), (((@PArith) (a))) -> (a) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordProj) (pa) ("mul"))).

Definition ecDiv : forall (a : Type), (((@PArith) (a))) -> (a) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordProj) (pa) ("div"))).

Definition ecMod : forall (a : Type), (((@PArith) (a))) -> (a) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordProj) (pa) ("mod"))).

Definition ecExp : forall (a : Type), (((@PArith) (a))) -> (a) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordProj) (pa) ("exp"))).

Definition ecLg2 : forall (a : Type), (((@PArith) (a))) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordProj) (pa) ("lg2"))).

Definition ecNeg : forall (a : Type), (((@PArith) (a))) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordProj) (pa) ("neg"))).

Definition ecSDiv : forall (a : Type), (((@PArith) (a))) -> (a) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordProj) (pa) ("sdiv"))).

Definition ecSMod : forall (a : Type), (((@PArith) (a))) -> (a) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) => ((RecordProj) (pa) ("smod"))).

Definition ecLt : forall (a : Type), (((@PCmp) (a))) -> (a) -> (a) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("cmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (((RecordTypeCons) ("eq") ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))))) (x : a) (y : a) => ((((RecordProj) (pa) ("cmp"))) (x) (y) (((@SAWCoreScaffolding.false))))).

Definition ecGt : forall (a : Type), (((@PCmp) (a))) -> (a) -> (a) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("cmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (((RecordTypeCons) ("eq") ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))))) (x : a) (y : a) => ((@ecLt) (a) (pa) (y) (x))).

Definition ecLtEq : forall (a : Type), (((@PCmp) (a))) -> (a) -> (a) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("cmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (((RecordTypeCons) ("eq") ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))))) (x : a) (y : a) => ((@SAWCoreScaffolding.not) (((@ecLt) (a) (pa) (y) (x))))).

Definition ecGtEq : forall (a : Type), (((@PCmp) (a))) -> (a) -> (a) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("cmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (((RecordTypeCons) ("eq") ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))))) (x : a) (y : a) => ((@SAWCoreScaffolding.not) (((@ecLt) (a) (pa) (x) (y))))).

Definition ecSLt : forall (a : Type), (((@PSignedCmp) (a))) -> (a) -> (a) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("scmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))) (x : a) (y : a) => ((((RecordProj) (pa) ("scmp"))) (x) (y) (((@SAWCoreScaffolding.false))))).

Definition ecEq : forall (a : Type), (((@PCmp) (a))) -> (a) -> (a) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("cmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (((RecordTypeCons) ("eq") ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))))) => ((RecordProj) (pa) ("eq"))).

Definition ecNotEq : forall (a : Type), (((@PCmp) (a))) -> (a) -> (a) -> ((@SAWCoreScaffolding.Bool)) :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("cmp") ((a) -> (a) -> (((@SAWCoreScaffolding.Bool))) -> ((@SAWCoreScaffolding.Bool))) (((RecordTypeCons) ("eq") ((a) -> (a) -> ((@SAWCoreScaffolding.Bool))) (RecordTypeNil))))) (x : a) (y : a) => ((@SAWCoreScaffolding.not) (((@ecEq) (a) (pa) (x) (y))))).

Definition ecAnd : forall (a : Type), (((@PLogic) (a))) -> (a) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("and") ((a) -> (a) -> a) (((RecordTypeCons) ("not") ((a) -> a) (((RecordTypeCons) ("or") ((a) -> (a) -> a) (((RecordTypeCons) ("xor") ((a) -> (a) -> a) (RecordTypeNil))))))))) => ((RecordProj) (pa) ("and"))).

Definition ecOr : forall (a : Type), (((@PLogic) (a))) -> (a) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("and") ((a) -> (a) -> a) (((RecordTypeCons) ("not") ((a) -> a) (((RecordTypeCons) ("or") ((a) -> (a) -> a) (((RecordTypeCons) ("xor") ((a) -> (a) -> a) (RecordTypeNil))))))))) => ((RecordProj) (pa) ("or"))).

Definition ecXor : forall (a : Type), (((@PLogic) (a))) -> (a) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("and") ((a) -> (a) -> a) (((RecordTypeCons) ("not") ((a) -> a) (((RecordTypeCons) ("or") ((a) -> (a) -> a) (((RecordTypeCons) ("xor") ((a) -> (a) -> a) (RecordTypeNil))))))))) => ((RecordProj) (pa) ("xor"))).

Definition ecCompl : forall (a : Type), (((@PLogic) (a))) -> (a) -> a :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("and") ((a) -> (a) -> a) (((RecordTypeCons) ("not") ((a) -> a) (((RecordTypeCons) ("or") ((a) -> (a) -> a) (((RecordTypeCons) ("xor") ((a) -> (a) -> a) (RecordTypeNil))))))))) => ((RecordProj) (pa) ("not"))).

Definition ecZero : forall (a : Type), (((@PZero) (a))) -> a :=
  (fun (a : Type) (pa : a) => pa).

Definition ecShiftL : forall (m : ((@Num))), forall (n : ((@Num))), forall (a : Type), (((@PZero) (a))) -> (((@seq) (m) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (m) (a)) :=
  (fun (m : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (m : ((@Num))) => forall (n : ((@Num))), forall (a : Type), (((@PZero) (a))) -> (((@seq) (m) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (m) (a)))) ((fun (m : ((@SAWCoreScaffolding.Nat))) => ((@finNumRec) ((fun (n : ((@Num))) => forall (a : Type), (((@PZero) (a))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (pz : a) => ((@SAWCorePrelude.bvShiftL) (m) (a) (n) (((@ecZero) (a) (pz))))))))) (((@finNumRec) ((fun (n : ((@Num))) => forall (a : Type), (((@PZero) (a))) -> (((@SAWCorePrelude.Stream) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCorePrelude.Stream) (a)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (pz : a) => ((@SAWCorePrelude.bvStreamShiftL) (a) (n)))))) (m))).

Definition ecShiftR : forall (m : ((@Num))), forall (n : ((@Num))), forall (a : Type), (((@PZero) (a))) -> (((@seq) (m) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (m) (a)) :=
  (fun (m : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (m : ((@Num))) => forall (n : ((@Num))), forall (a : Type), (((@PZero) (a))) -> (((@seq) (m) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (m) (a)))) ((fun (m : ((@SAWCoreScaffolding.Nat))) => ((@finNumRec) ((fun (n : ((@Num))) => forall (a : Type), (((@PZero) (a))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (pz : a) => ((@SAWCorePrelude.bvShiftR) (m) (a) (n) (((@ecZero) (a) (pz))))))))) (((@finNumRec) ((fun (n : ((@Num))) => forall (a : Type), (((@PZero) (a))) -> (((@SAWCorePrelude.Stream) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCorePrelude.Stream) (a)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (pz : a) => ((@SAWCorePrelude.bvStreamShiftR) (a) (n) (((@ecZero) (a) (pz)))))))) (m))).

Definition ecSShiftR : forall (n : ((@Num))), forall (k : ((@Num))), (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (k) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (n) (((@SAWCoreScaffolding.Bool)))) :=
  ((@finNumRec) ((fun (n : ((@Num))) => forall (k : ((@Num))), (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (k) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (n) (((@SAWCoreScaffolding.Bool)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@finNumRec) ((fun (k : ((@Num))) => (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (k) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCoreScaffolding.Bool)))))) ((fun (k : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.natCase) ((fun (w : ((@SAWCoreScaffolding.Nat))) => (((@SAWCorePrelude.bitvector) (w))) -> (((@SAWCorePrelude.bitvector) (k))) -> ((@SAWCorePrelude.bitvector) (w)))) ((fun (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (0) (((@SAWCoreScaffolding.Bool))))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (k) (((@SAWCoreScaffolding.Bool))))) => x)) ((fun (w : ((@SAWCoreScaffolding.Nat))) (x : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (w))) (((@SAWCoreScaffolding.Bool))))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (k) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreVectorsAsCoqVectors.bvSShr) (w) (x) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (k) (i)))))) (n)))))))).

Definition ecCarry : forall (n : ((@Num))), (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)) :=
  ((@finNumRec) ((fun (n : ((@Num))) => (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)))) (((@SAWCorePrelude.bvCarry)))).

Definition ecSCarry : forall (n : ((@Num))), (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)) :=
  ((@finNumRec) ((fun (n : ((@Num))) => (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.natCase) ((fun (w : ((@SAWCoreScaffolding.Nat))) => (((@SAWCorePrelude.bitvector) (w))) -> (((@SAWCorePrelude.bitvector) (w))) -> ((@SAWCoreScaffolding.Bool)))) ((fun (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (0) (((@SAWCoreScaffolding.Bool))))) (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (0) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreScaffolding.error) (((@SAWCoreScaffolding.Bool))) (("invalid SCarry instance")%string)))) (((@SAWCorePrelude.bvSCarry))) (n))))).

Definition ecRotL : forall (m : ((@Num))), forall (n : ((@Num))), forall (a : Type), (((@seq) (m) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (m) (a)) :=
  ((@finNumRec2) ((fun (m : ((@Num))) (n : ((@Num))) => forall (a : Type), (((@seq) (m) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (m) (a)))) ((fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (a : Type) => ((@SAWCorePrelude.bvRotateL) (m) (a) (n))))).

Definition ecRotR : forall (m : ((@Num))), forall (n : ((@Num))), forall (a : Type), (((@seq) (m) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (m) (a)) :=
  ((@finNumRec2) ((fun (m : ((@Num))) (n : ((@Num))) => forall (a : Type), (((@seq) (m) (a))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (m) (a)))) ((fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) (a : Type) => ((@SAWCorePrelude.bvRotateR) (m) (a) (n))))).

Definition ecCat : forall (m : ((@Num))), forall (n : ((@Num))), forall (a : Type), (((@seq) (m) (a))) -> (((@seq) (n) (a))) -> ((@seq) (((@tcAdd) (m) (n))) (a)) :=
  ((@finNumRec) ((fun (m : ((@Num))) => forall (n : ((@Num))), forall (a : Type), (((@seq) (m) (a))) -> (((@seq) (n) (a))) -> ((@seq) (((@tcAdd) (m) (n))) (a)))) ((fun (m : ((@SAWCoreScaffolding.Nat))) => ((@CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) -> (((@seq) (n) (a))) -> ((@seq) (((@tcAdd) (((@TCNum) (m))) (n))) (a)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) => ((@SAWCorePrelude.append) (m) (n) (a)))) ((fun (a : Type) => ((@SAWCorePrelude.streamAppend) (a) (m)))))))).

Definition ecSplitAt : forall (m : ((@Num))), forall (n : ((@Num))), forall (a : Type), (((@seq) (((@tcAdd) (m) (n))) (a))) -> ((prod) (((@seq) (m) (a))) (((@seq) (n) (a)))) :=
  ((@finNumRec) ((fun (m : ((@Num))) => forall (n : ((@Num))), forall (a : Type), (((@seq) (((@tcAdd) (m) (n))) (a))) -> ((prod) (((@seq) (m) (a))) (((@seq) (n) (a)))))) ((fun (m : ((@SAWCoreScaffolding.Nat))) => ((@CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => forall (a : Type), (((@seq) (((@tcAdd) (((@TCNum) (m))) (n))) (a))) -> ((prod) (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) (((@seq) (n) (a)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCorePrelude.addNat) (m) (n))) (a))) => ((pair) (((@SAWCorePrelude.take) (a) (m) (n) (xs))) (((@SAWCorePrelude.drop) (a) (m) (n) (xs)))))) ((fun (a : Type) (xs : ((@SAWCorePrelude.Stream) (a))) => ((pair) (((@SAWCorePrelude.streamTake) (a) (m) (xs))) (((@SAWCorePrelude.streamDrop) (a) (m) (xs)))))))))).

Definition ecJoin : forall (m : ((@Num))), forall (n : ((@Num))), forall (a : Type), (((@seq) (m) (((@seq) (n) (a))))) -> ((@seq) (((@tcMul) (m) (n))) (a)) :=
  (fun (m : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (m : ((@Num))) => forall (n : ((@Num))), forall (a : Type), (((@seq) (m) (((@seq) (n) (a))))) -> ((@seq) (((@tcMul) (m) (n))) (a)))) ((fun (m : ((@SAWCoreScaffolding.Nat))) => ((@finNumRec) ((fun (n : ((@Num))) => forall (a : Type), (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@seq) (n) (a))))) -> ((@seq) (((@tcMul) (((@TCNum) (m))) (n))) (a)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) => ((@SAWCorePrelude.join) (m) (n) (a))))))) (((@finNumRec) ((fun (n : ((@Num))) => forall (a : Type), (((@SAWCorePrelude.Stream) (((@seq) (n) (a))))) -> ((@seq) (((@tcMul) (((@TCInf))) (n))) (a)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) => ((@SAWCorePrelude.natCase) ((fun (n' : ((@SAWCoreScaffolding.Nat))) => (((@SAWCorePrelude.Stream) (((@SAWCoreVectorsAsCoqVectors.Vec) (n') (a))))) -> ((@seq) (((@SAWCorePrelude.if0Nat) (((@Num))) (n') (((@TCNum) (0))) (((@TCInf))))) (a)))) ((fun (s : ((@SAWCorePrelude.Stream) (((@SAWCoreVectorsAsCoqVectors.Vec) (0) (a))))) => ((@SAWCoreVectorsAsCoqVectors.EmptyVec) (a)))) ((fun (n' : ((@SAWCoreScaffolding.Nat))) (s : ((@SAWCorePrelude.Stream) (((@SAWCoreVectorsAsCoqVectors.Vec) (((@SAWCoreScaffolding.Succ) (n'))) (a))))) => ((@SAWCorePrelude.streamJoin) (a) (n') (s)))) (n)))))) (m))).

Definition ecSplit : forall (m : ((@Num))), forall (n : ((@Num))), forall (a : Type), (((@seq) (((@tcMul) (m) (n))) (a))) -> ((@seq) (m) (((@seq) (n) (a)))) :=
  (fun (m : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (m : ((@Num))) => forall (n : ((@Num))), forall (a : Type), (((@seq) (((@tcMul) (m) (n))) (a))) -> ((@seq) (m) (((@seq) (n) (a)))))) ((fun (m : ((@SAWCoreScaffolding.Nat))) => ((@finNumRec) ((fun (n : ((@Num))) => forall (a : Type), (((@seq) (((@tcMul) (((@TCNum) (m))) (n))) (a))) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@seq) (n) (a)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) => ((@SAWCorePrelude.split) (m) (n) (a))))))) (((@finNumRec) ((fun (n : ((@Num))) => forall (a : Type), (((@seq) (((@tcMul) (((@TCInf))) (n))) (a))) -> ((@SAWCorePrelude.Stream) (((@seq) (n) (a)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) => ((@SAWCorePrelude.natCase) ((fun (n' : ((@SAWCoreScaffolding.Nat))) => (((@seq) (((@SAWCorePrelude.if0Nat) (((@Num))) (n') (((@TCNum) (0))) (((@TCInf))))) (a))) -> ((@SAWCorePrelude.Stream) (((@SAWCoreVectorsAsCoqVectors.Vec) (n') (a)))))) (((@SAWCorePrelude.streamConst) (((@SAWCoreVectorsAsCoqVectors.Vec) (0) (a))))) ((fun (n' : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.streamSplit) (a) (((@SAWCoreScaffolding.Succ) (n')))))) (n)))))) (m))).

Definition ecReverse : forall (n : ((@Num))), forall (a : Type), (((@seq) (n) (a))) -> ((@seq) (n) (a)) :=
  ((@finNumRec) ((fun (n : ((@Num))) => forall (a : Type), (((@seq) (n) (a))) -> ((@seq) (n) (a)))) (((@SAWCorePrelude.reverse)))).

Definition ecTranspose : forall (m : ((@Num))), forall (n : ((@Num))), forall (a : Type), (((@seq) (m) (((@seq) (n) (a))))) -> ((@seq) (n) (((@seq) (m) (a)))) :=
  (fun (m : ((@Num))) (n : ((@Num))) (a : Type) => ((CryptolPrimitives.Num_rect) ((fun (m : ((@Num))) => (((@seq) (m) (((@seq) (n) (a))))) -> ((@seq) (n) (((@seq) (m) (a)))))) ((fun (m : ((@SAWCoreScaffolding.Nat))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@seq) (n) (a))))) -> ((@seq) (n) (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.transpose) (m) (n) (a)))) ((fun (xss : ((@SAWCoreVectorsAsCoqVectors.Vec) (m) (((@SAWCorePrelude.Stream) (a))))) => ((@SAWCorePrelude.MkStream) (((@SAWCoreVectorsAsCoqVectors.Vec) (m) (a))) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.gen) (m) (a) ((fun (j : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.streamGet) (a) (((@SAWCorePrelude.sawAt) (m) (((@SAWCorePrelude.Stream) (a))) (xss) (j))) (i)))))))))) (n)))) (((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (((@SAWCorePrelude.Stream) (((@seq) (n) (a))))) -> ((@seq) (n) (((@SAWCorePrelude.Stream) (a)))))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (xss : ((@SAWCorePrelude.Stream) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))))) => ((@SAWCoreVectorsAsCoqVectors.gen) (n) (((@SAWCorePrelude.Stream) (a))) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.MkStream) (a) ((fun (j : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.sawAt) (n) (a) (((@SAWCorePrelude.streamGet) (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (xss) (j))) (i)))))))))) ((fun (xss : ((@SAWCorePrelude.Stream) (((@SAWCorePrelude.Stream) (a))))) => ((@SAWCorePrelude.MkStream) (((@SAWCorePrelude.Stream) (a))) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.MkStream) (a) ((fun (j : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.streamGet) (a) (((@SAWCorePrelude.streamGet) (((@SAWCorePrelude.Stream) (a))) (xss) (j))) (i)))))))))) (n))) (m))).

Definition ecAt : forall (n : ((@Num))), forall (a : Type), forall (i : ((@Num))), (((@seq) (n) (a))) -> (((@seq) (i) (((@SAWCoreScaffolding.Bool))))) -> a :=
  (fun (n : ((@Num))) (a : Type) (i : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (i : ((@Num))) => (((@seq) (n) (a))) -> (((@seq) (i) (((@SAWCoreScaffolding.Bool))))) -> a)) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => (((@seq) (n) (a))) -> (((@SAWCoreVectorsAsCoqVectors.Vec) (i) (((@SAWCoreScaffolding.Bool))))) -> a)) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.bvAt) (n) (a) (i)))) (((@SAWCorePrelude.bvStreamGet) (a) (i))) (n)))) (((@SAWCoreScaffolding.error) ((((@seq) (n) (a))) -> (((@SAWCorePrelude.Stream) (((@SAWCoreScaffolding.Bool))))) -> a) (("Unexpected Fin constraint violation!")%string))) (i))).

Definition ecAtBack : forall (n : ((@Num))), forall (a : Type), forall (i : ((@Num))), (((@seq) (n) (a))) -> (((@seq) (i) (((@SAWCoreScaffolding.Bool))))) -> a :=
  (fun (n : ((@Num))) (a : Type) (i : ((@Num))) (xs : ((CryptolPrimitives.Num_rect) ((fun (num : ((@Num))) => Type)) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) (((@SAWCorePrelude.Stream) (a))) (n))) => ((@ecAt) (n) (a) (i) (((@ecReverse) (n) (a) (xs))))).

Definition ecFromTo : forall (first : ((@Num))), forall (last : ((@Num))), forall (a : Type), (((@PLiteral) (a))) -> ((@seq) (((@tcAdd) (((@TCNum) (1))) (((@tcSub) (last) (first))))) (a)) :=
  ((@finNumRec) ((fun (first : ((@Num))) => forall (last : ((@Num))), forall (a : Type), (((@PLiteral) (a))) -> ((@seq) (((@tcAdd) (((@TCNum) (1))) (((@tcSub) (last) (first))))) (a)))) ((fun (first : ((@SAWCoreScaffolding.Nat))) => ((@finNumRec) ((fun (last : ((@Num))) => forall (a : Type), (((@PLiteral) (a))) -> ((@seq) (((@tcAdd) (((@TCNum) (1))) (((@tcSub) (last) (((@TCNum) (first))))))) (a)))) ((fun (last : ((@SAWCoreScaffolding.Nat))) (a : Type) (pa : (((@SAWCoreScaffolding.Nat))) -> a) => ((@SAWCoreVectorsAsCoqVectors.gen) (((@SAWCorePrelude.addNat) (1) (((@SAWCorePrelude.subNat) (last) (first))))) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((pa) (((@SAWCorePrelude.addNat) (i) (first))))))))))))).

Definition ecFromThenTo : forall (first : ((@Num))), forall (next : ((@Num))), forall (last : ((@Num))), forall (a : Type), forall (len : ((@Num))), (((@PLiteral) (a))) -> (((@PLiteral) (a))) -> (((@PLiteral) (a))) -> ((@seq) (len) (a)) :=
  (fun (first : ((@Num))) (next : ((@Num))) (_ : ((@Num))) (a : Type) => ((@finNumRec) ((fun (len : ((@Num))) => (((@PLiteral) (a))) -> (((@PLiteral) (a))) -> (((@PLiteral) (a))) -> ((@seq) (len) (a)))) ((fun (len : ((@SAWCoreScaffolding.Nat))) (pa : (((@SAWCoreScaffolding.Nat))) -> a) (_ : (((@SAWCoreScaffolding.Nat))) -> a) (_ : (((@SAWCoreScaffolding.Nat))) -> a) => ((@SAWCoreVectorsAsCoqVectors.gen) (len) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((pa) (((@SAWCorePrelude.subNat) (((@SAWCorePrelude.addNat) (((@getFinNat) (first))) (((@SAWCorePrelude.mulNat) (i) (((@getFinNat) (next))))))) (((@SAWCorePrelude.mulNat) (i) (((@getFinNat) (first))))))))))))))).

Definition ecInfFrom : forall (a : Type), (((@PArith) (a))) -> (a) -> ((@seq) (((@TCInf))) (a)) :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) (x : a) => ((@SAWCorePrelude.MkStream) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((((RecordProj) (pa) ("add"))) (x) (((((RecordProj) (pa) ("int"))) (((@SAWCoreScaffolding.natToInt) (i)))))))))).

Definition ecInfFromThen : forall (a : Type), (((@PArith) (a))) -> (a) -> (a) -> ((@seq) (((@TCInf))) (a)) :=
  (fun (a : Type) (pa : ((RecordTypeCons) ("add") ((a) -> (a) -> a) (((RecordTypeCons) ("div") ((a) -> (a) -> a) (((RecordTypeCons) ("exp") ((a) -> (a) -> a) (((RecordTypeCons) ("int") ((((@SAWCoreScaffolding.Integer))) -> a) (((RecordTypeCons) ("lg2") ((a) -> a) (((RecordTypeCons) ("mod") ((a) -> (a) -> a) (((RecordTypeCons) ("mul") ((a) -> (a) -> a) (((RecordTypeCons) ("neg") ((a) -> a) (((RecordTypeCons) ("sdiv") ((a) -> (a) -> a) (((RecordTypeCons) ("smod") ((a) -> (a) -> a) (((RecordTypeCons) ("sub") ((a) -> (a) -> a) (RecordTypeNil))))))))))))))))))))))) (x : a) (y : a) => ((@SAWCorePrelude.MkStream) (a) ((fun (i : ((@SAWCoreScaffolding.Nat))) => ((((RecordProj) (pa) ("add"))) (x) (((((RecordProj) (pa) ("mul"))) (((((RecordProj) (pa) ("sub"))) (y) (x))) (((((RecordProj) (pa) ("int"))) (((@SAWCoreScaffolding.natToInt) (i)))))))))))).

Definition ecError : forall (a : Type), forall (len : ((@Num))), (((@seq) (len) (((@SAWCorePrelude.bitvector) (8))))) -> a :=
  (fun (a : Type) (len : ((@Num))) (msg : ((CryptolPrimitives.Num_rect) ((fun (num : ((@Num))) => Type)) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCorePrelude.bitvector) (8)))))) (((@SAWCorePrelude.Stream) (((@SAWCorePrelude.bitvector) (8))))) (len))) => ((@SAWCoreScaffolding.error) (a) (("encountered call to the Cryptol 'error' function")%string))).

Definition ecRandom : forall (a : Type), (((@SAWCorePrelude.bitvector) (32))) -> a :=
  (fun (a : Type) (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (32) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreScaffolding.error) (a) (("Cryptol.random")%string))).

Definition ecTrace : forall (n : ((@Num))), forall (a : Type), forall (b : Type), (((@seq) (n) (((@SAWCorePrelude.bitvector) (8))))) -> (a) -> (b) -> b :=
  (fun (_ : ((@Num))) (_ : Type) (_ : Type) (_ : ((CryptolPrimitives.Num_rect) ((fun (num : ((@Num))) => Type)) ((fun (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (((@SAWCorePrelude.bitvector) (8)))))) (((@SAWCorePrelude.Stream) (((@SAWCorePrelude.bitvector) (8))))) (_))) (_ : _) (x : _) => x).

Definition ecUpdate : forall (n : ((@Num))), forall (a : Type), forall (w : ((@Num))), (((@seq) (n) (a))) -> (((@seq) (w) (((@SAWCoreScaffolding.Bool))))) -> (a) -> ((@seq) (n) (a)) :=
  (fun (n : ((@Num))) => ((CryptolPrimitives.Num_rect) ((fun (n : ((@Num))) => forall (a : Type), forall (w : ((@Num))), (((@seq) (n) (a))) -> (((@seq) (w) (((@SAWCoreScaffolding.Bool))))) -> (a) -> ((@seq) (n) (a)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) => ((@finNumRec) ((fun (w : ((@Num))) => (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@seq) (w) (((@SAWCoreScaffolding.Bool))))) -> (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) ((fun (w : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.bvUpd) (n) (a) (w))))))) ((fun (a : Type) => ((@finNumRec) ((fun (w : ((@Num))) => (((@SAWCorePrelude.Stream) (a))) -> (((@seq) (w) (((@SAWCoreScaffolding.Bool))))) -> (a) -> ((@SAWCorePrelude.Stream) (a)))) ((fun (w : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.bvStreamUpd) (a) (w))))))) (n))).

Definition ecUpdateEnd : forall (n : ((@Num))), forall (a : Type), forall (w : ((@Num))), (((@seq) (n) (a))) -> (((@seq) (w) (((@SAWCoreScaffolding.Bool))))) -> (a) -> ((@seq) (n) (a)) :=
  ((@finNumRec) ((fun (n : ((@Num))) => forall (a : Type), forall (w : ((@Num))), (((@seq) (n) (a))) -> (((@seq) (w) (((@SAWCoreScaffolding.Bool))))) -> (a) -> ((@seq) (n) (a)))) ((fun (n : ((@SAWCoreScaffolding.Nat))) (a : Type) => ((@finNumRec) ((fun (w : ((@Num))) => (((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) -> (((@seq) (w) (((@SAWCoreScaffolding.Bool))))) -> (a) -> ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a)))) ((fun (w : ((@SAWCoreScaffolding.Nat))) (xs : ((@SAWCoreVectorsAsCoqVectors.Vec) (n) (a))) (i : ((@SAWCoreVectorsAsCoqVectors.Vec) (w) (((@SAWCoreScaffolding.Bool))))) (y : a) => ((@SAWCorePrelude.upd) (n) (a) (xs) (((@SAWCorePrelude.subNat) (((@SAWCorePrelude.subNat) (n) (1))) (((@SAWCoreVectorsAsCoqVectors.bvToNat) (w) (i))))) (y)))))))).

Definition ecTrunc : forall (m : ((@Num))), forall (n : ((@Num))), (((@seq) (((@tcAdd) (m) (n))) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (n) (((@SAWCoreScaffolding.Bool)))) :=
  ((@finNumRec2) ((fun (m : ((@Num))) (n : ((@Num))) => (((@seq) (((@tcAdd) (m) (n))) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (n) (((@SAWCoreScaffolding.Bool)))))) (((@SAWCorePrelude.bvTrunc)))).

Definition ecUExt : forall (m : ((@Num))), forall (n : ((@Num))), (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (((@tcAdd) (m) (n))) (((@SAWCoreScaffolding.Bool)))) :=
  ((@finNumRec2) ((fun (m : ((@Num))) (n : ((@Num))) => (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (((@tcAdd) (m) (n))) (((@SAWCoreScaffolding.Bool)))))) (((@SAWCorePrelude.bvUExt)))).

Definition ecSExt : forall (m : ((@Num))), forall (n : ((@Num))), (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (((@tcAdd) (m) (n))) (((@SAWCoreScaffolding.Bool)))) :=
  ((@finNumRec2) ((fun (m : ((@Num))) (n : ((@Num))) => (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@seq) (((@tcAdd) (m) (n))) (((@SAWCoreScaffolding.Bool)))))) ((fun (m : ((@SAWCoreScaffolding.Nat))) (n : ((@SAWCoreScaffolding.Nat))) => ((@SAWCorePrelude.natCase) ((fun (n' : ((@SAWCoreScaffolding.Nat))) => (((@SAWCorePrelude.bitvector) (n'))) -> ((@SAWCorePrelude.bitvector) (((@SAWCorePrelude.addNat) (m) (n')))))) ((fun (_ : ((@SAWCoreVectorsAsCoqVectors.Vec) (0) (((@SAWCoreScaffolding.Bool))))) => ((@SAWCoreVectorsAsCoqVectors.bvNat) (((@SAWCorePrelude.addNat) (m) (0))) (0)))) (((@SAWCorePrelude.bvSExt) (m))) (n))))).

Definition ecSgt : forall (n : ((@Num))), (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)) :=
  ((@finNumRec) ((fun (n : ((@Num))) => (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)))) (((@SAWCoreVectorsAsCoqVectors.bvsgt)))).

Definition ecSge : forall (n : ((@Num))), (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)) :=
  ((@finNumRec) ((fun (n : ((@Num))) => (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)))) (((@SAWCoreVectorsAsCoqVectors.bvsge)))).

Definition ecSlt : forall (n : ((@Num))), (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)) :=
  ((@finNumRec) ((fun (n : ((@Num))) => (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)))) (((@SAWCoreVectorsAsCoqVectors.bvslt)))).

Definition ecSle : forall (n : ((@Num))), (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)) :=
  ((@finNumRec) ((fun (n : ((@Num))) => (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> (((@seq) (n) (((@SAWCoreScaffolding.Bool))))) -> ((@SAWCoreScaffolding.Bool)))) (((@SAWCoreVectorsAsCoqVectors.bvsle)))).

Axiom replicate_False : forall (n : ((@SAWCoreScaffolding.Nat))), ((@SAWCoreScaffolding.Eq) (((@SAWCorePrelude.bitvector) (n))) (((@SAWCorePrelude.replicate) (n) (((@SAWCoreScaffolding.Bool))) (((@SAWCoreScaffolding.false))))) (((@SAWCoreVectorsAsCoqVectors.bvNat) (n) (0)))) .

Axiom subNat_0 : forall (n : ((@SAWCoreScaffolding.Nat))), ((@SAWCoreScaffolding.Eq) (((@SAWCoreScaffolding.Nat))) (((@SAWCorePrelude.subNat) (n) (0))) (n)) .

End CryptolPrimitives.
