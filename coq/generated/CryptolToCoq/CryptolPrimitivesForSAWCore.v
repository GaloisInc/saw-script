
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.

Import ListNotations.

Module CryptolPrimitives.

Definition const : forall (a : Type), forall (b : Type), a -> b -> a :=
  fun (a : Type) (b : Type) (x : a) (y : b) => x.

Definition compose : forall (a : Type), forall (b : Type), forall (c : Type), (b -> c) -> (a -> b) -> a -> c :=
  fun (_1 : Type) (_2 : Type) (_3 : Type) (f : _2 -> _3) (g : _1 -> _2) (x : _1) => f (g x).

Definition bvExp : forall (n : @SAWCoreScaffolding.Nat), @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool) :=
  fun (n : @SAWCoreScaffolding.Nat) (x : @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) (y : @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) => @SAWCoreVectorsAsCoqVectors.foldr (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) n (fun (b : @SAWCoreScaffolding.Bool) (a : @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) => if b then @SAWCoreVectorsAsCoqVectors.bvMul n x (@SAWCoreVectorsAsCoqVectors.bvMul n a a) else @SAWCoreVectorsAsCoqVectors.bvMul n a a) (@SAWCoreVectorsAsCoqVectors.bvNat n 1) (@SAWCorePrelude.reverse n (@SAWCoreScaffolding.Bool) y).

Definition updFst : forall (a : Type), forall (b : Type), (a -> a) -> prod a b -> prod a b :=
  fun (a : Type) (b : Type) (f : a -> a) (x : prod a b) => pair (f (SAWCoreScaffolding.fst x)) (SAWCoreScaffolding.snd x).

Definition updSnd : forall (a : Type), forall (b : Type), (b -> b) -> prod a b -> prod a b :=
  fun (a : Type) (b : Type) (f : b -> b) (x : prod a b) => pair (SAWCoreScaffolding.fst x) (f (SAWCoreScaffolding.snd x)).

Inductive Num : Type :=
| TCNum : @SAWCoreScaffolding.Nat -> @Num
| TCInf : @Num
.

(* Cryptol.Num_rec was skipped *)

Definition getFinNat : forall (n : @Num), @SAWCoreScaffolding.Nat :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @SAWCoreScaffolding.Nat) (fun (n1 : @SAWCoreScaffolding.Nat) => n1) (@SAWCoreScaffolding.error (@SAWCoreScaffolding.Nat) "Unexpected Fin constraint violation!"%string) n.

Definition finNumRec : forall (p : @Num -> Type), (forall (n : @SAWCoreScaffolding.Nat), p (@TCNum n)) -> forall (n : @Num), p n :=
  fun (p : @Num -> Type) (f : forall (n : @SAWCoreScaffolding.Nat), p (@TCNum n)) (n : @Num) => CryptolPrimitives.Num_rect p f (@SAWCoreScaffolding.error (p (@TCInf)) "Unexpected Fin constraint violation!"%string) n.

Definition finNumRec2 : forall (p : @Num -> @Num -> Type), (forall (m : @SAWCoreScaffolding.Nat), forall (n : @SAWCoreScaffolding.Nat), p (@TCNum m) (@TCNum n)) -> forall (m : @Num), forall (n : @Num), p m n :=
  fun (p : @Num -> @Num -> Type) (f : forall (m : @SAWCoreScaffolding.Nat), forall (n : @SAWCoreScaffolding.Nat), p (@TCNum m) (@TCNum n)) => @finNumRec (fun (m : @Num) => forall (n : @Num), p m n) (fun (m : @SAWCoreScaffolding.Nat) => @finNumRec (p (@TCNum m)) (f m)).

Definition binaryNumFun : (@SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat) -> (@SAWCoreScaffolding.Nat -> @Num) -> (@SAWCoreScaffolding.Nat -> @Num) -> @Num -> @Num -> @Num -> @Num :=
  fun (f1 : @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat) (f2 : @SAWCoreScaffolding.Nat -> @Num) (f3 : @SAWCoreScaffolding.Nat -> @Num) (f4 : @Num) (num1 : @Num) (num2 : @Num) => CryptolPrimitives.Num_rect (fun (num1' : @Num) => @Num) (fun (n1 : @SAWCoreScaffolding.Nat) => CryptolPrimitives.Num_rect (fun (num2' : @Num) => @Num) (fun (n2 : @SAWCoreScaffolding.Nat) => @TCNum (f1 n1 n2)) (f2 n1) num2) (CryptolPrimitives.Num_rect (fun (num2' : @Num) => @Num) f3 f4 num2) num1.

Definition ternaryNumFun : (@SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat) -> @Num -> @Num -> @Num -> @Num -> @Num :=
  fun (f1 : @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat) (f2 : @Num) (num1 : @Num) (num2 : @Num) (num3 : @Num) => CryptolPrimitives.Num_rect (fun (num1' : @Num) => @Num) (fun (n1 : @SAWCoreScaffolding.Nat) => CryptolPrimitives.Num_rect (fun (num2' : @Num) => @Num) (fun (n2 : @SAWCoreScaffolding.Nat) => CryptolPrimitives.Num_rect (fun (num3' : @Num) => @Num) (fun (n3 : @SAWCoreScaffolding.Nat) => @TCNum (f1 n1 n2 n3)) f2 num3) f2 num2) f2 num1.

Definition tcWidth : @Num -> @Num :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @Num) (fun (x : @SAWCoreScaffolding.Nat) => @TCNum (@SAWCoreScaffolding.widthNat x)) (@TCInf) n.

Definition tcAdd : @Num -> @Num -> @Num :=
  @binaryNumFun (@SAWCorePrelude.addNat) (fun (x : @SAWCoreScaffolding.Nat) => @TCInf) (fun (y : @SAWCoreScaffolding.Nat) => @TCInf) (@TCInf).

Definition tcSub : @Num -> @Num -> @Num :=
  @binaryNumFun (@SAWCorePrelude.subNat) (fun (x : @SAWCoreScaffolding.Nat) => @TCNum 0) (fun (y : @SAWCoreScaffolding.Nat) => @TCInf) (@TCNum 0).

Definition tcMul : @Num -> @Num -> @Num :=
  @binaryNumFun (@SAWCorePrelude.mulNat) (fun (x : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.if0Nat (@Num) x (@TCNum 0) (@TCInf)) (fun (y : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.if0Nat (@Num) y (@TCNum 0) (@TCInf)) (@TCInf).

Definition tcDiv : @Num -> @Num -> @Num :=
  @binaryNumFun (fun (x : @SAWCoreScaffolding.Nat) (y : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.divNat x y) (fun (x : @SAWCoreScaffolding.Nat) => @TCNum 0) (fun (y : @SAWCoreScaffolding.Nat) => @TCInf) (@TCNum 1).

Definition tcMod : @Num -> @Num -> @Num :=
  @binaryNumFun (fun (x : @SAWCoreScaffolding.Nat) (y : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.modNat x y) (fun (x : @SAWCoreScaffolding.Nat) => @TCNum 0) (fun (y : @SAWCoreScaffolding.Nat) => @TCNum 0) (@TCNum 0).

Definition tcExp : @Num -> @Num -> @Num :=
  @binaryNumFun (@SAWCorePrelude.expNat) (fun (x : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.natCase (fun (_1 : @SAWCoreScaffolding.Nat) => @Num) (@TCNum 0) (fun (x_minus_1 : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.if0Nat (@Num) x_minus_1 (@TCNum 1) (@TCInf)) x) (fun (y : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.if0Nat (@Num) y (@TCNum 1) (@TCInf)) (@TCInf).

Definition tcMin : @Num -> @Num -> @Num :=
  @binaryNumFun (@SAWCorePrelude.minNat) (fun (x : @SAWCoreScaffolding.Nat) => @TCNum x) (fun (y : @SAWCoreScaffolding.Nat) => @TCNum y) (@TCInf).

Definition tcMax : @Num -> @Num -> @Num :=
  @binaryNumFun (@SAWCorePrelude.maxNat) (fun (x : @SAWCoreScaffolding.Nat) => @TCInf) (fun (y : @SAWCoreScaffolding.Nat) => @TCInf) (@TCInf).

Definition ceilDivNat : @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat :=
  fun (x : @SAWCoreScaffolding.Nat) (y : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.divNat (@SAWCorePrelude.addNat x (@SAWCorePrelude.subNat y 1)) y.

Definition ceilModNat : @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat :=
  fun (x : @SAWCoreScaffolding.Nat) (y : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.subNat (@SAWCorePrelude.mulNat (@ceilDivNat x y) y) x.

Definition tcCeilDiv : @Num -> @Num -> @Num :=
  @binaryNumFun (@ceilDivNat) (fun (x : @SAWCoreScaffolding.Nat) => @TCNum 0) (fun (y : @SAWCoreScaffolding.Nat) => @TCInf) (@TCInf).

Definition tcCeilMod : @Num -> @Num -> @Num :=
  @binaryNumFun (@ceilModNat) (fun (x : @SAWCoreScaffolding.Nat) => @TCNum 0) (fun (y : @SAWCoreScaffolding.Nat) => @TCInf) (@TCInf).

Definition tcLenFromThenTo_Nat : @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat -> @SAWCoreScaffolding.Nat :=
  fun (x : @SAWCoreScaffolding.Nat) (y : @SAWCoreScaffolding.Nat) (z : @SAWCoreScaffolding.Nat) => if @SAWCorePrelude.ltNat x y then if @SAWCorePrelude.ltNat z x then 0 else @SAWCorePrelude.addNat (@SAWCorePrelude.divNat (@SAWCorePrelude.subNat z x) (@SAWCorePrelude.subNat y x)) 1 else if @SAWCorePrelude.ltNat x z then 0 else @SAWCorePrelude.addNat (@SAWCorePrelude.divNat (@SAWCorePrelude.subNat x z) (@SAWCorePrelude.subNat x y)) 1.

Definition tcLenFromThenTo : @Num -> @Num -> @Num -> @Num :=
  @ternaryNumFun (@tcLenFromThenTo_Nat) (@TCInf).

Definition seq : @Num -> Type -> Type :=
  fun (num : @Num) (a : Type) => CryptolPrimitives.Num_rect (fun (num1 : @Num) => Type) (fun (n : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.Vec n a) (@SAWCorePrelude.Stream a) num.

Definition seq_TCNum : forall (n : @SAWCoreScaffolding.Nat), forall (a : Type), @SAWCoreScaffolding.Eq Type (@seq (@TCNum n) a) (@SAWCoreVectorsAsCoqVectors.Vec n a) :=
  fun (n : @SAWCoreScaffolding.Nat) (a : Type) => @SAWCoreScaffolding.Refl Type (@SAWCoreVectorsAsCoqVectors.Vec n a).

Definition seq_TCInf : forall (a : Type), @SAWCoreScaffolding.Eq Type (@seq (@TCInf) a) (@SAWCorePrelude.Stream a) :=
  fun (a : Type) => @SAWCoreScaffolding.Refl Type (@SAWCorePrelude.Stream a).

Definition seqMap : forall (a : Type), forall (b : Type), forall (n : @Num), (a -> b) -> @seq n a -> @seq n b :=
  fun (a : Type) (b : Type) (num : @Num) (f : a -> b) => CryptolPrimitives.Num_rect (fun (n : @Num) => @seq n a -> @seq n b) (@SAWCorePrelude.map a b f) (@SAWCorePrelude.streamMap a b f) num.

Definition seqConst : forall (n : @Num), forall (a : Type), a -> @seq n a :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => forall (a : Type), a -> @seq n1 a) (@SAWCorePrelude.replicate) (@SAWCorePrelude.streamConst) n.

Definition IntModNum : forall (num : @Num), Type :=
  fun (num : @Num) => CryptolPrimitives.Num_rect (fun (n : @Num) => Type) (@SAWCoreScaffolding.IntMod) (@SAWCoreScaffolding.Integer) num.

Definition Rational : Type :=
  unit.

Definition ecRatio : @SAWCoreScaffolding.Integer -> @SAWCoreScaffolding.Integer -> @Rational :=
  fun (x : @SAWCoreScaffolding.Integer) (y : @SAWCoreScaffolding.Integer) => tt.

Definition eqRational : @Rational -> @Rational -> @SAWCoreScaffolding.Bool :=
  fun (x : unit) (y : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Bool) "Unimplemented: (==) Rational"%string.

Definition ltRational : @Rational -> @Rational -> @SAWCoreScaffolding.Bool :=
  fun (x : unit) (y : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Bool) "Unimplemented: (<) Rational"%string.

Definition addRational : @Rational -> @Rational -> @Rational :=
  fun (x : unit) (y : unit) => @SAWCoreScaffolding.error (@Rational) "Unimplemented: (+) Rational"%string.

Definition subRational : @Rational -> @Rational -> @Rational :=
  fun (x : unit) (y : unit) => @SAWCoreScaffolding.error (@Rational) "Unimplemented: (-) Rational"%string.

Definition mulRational : @Rational -> @Rational -> @Rational :=
  fun (x : unit) (y : unit) => @SAWCoreScaffolding.error (@Rational) "Unimplemented: (*) Rational"%string.

Definition negRational : @Rational -> @Rational :=
  fun (x : unit) => @SAWCoreScaffolding.error (@Rational) "Unimplemented: negate Rational"%string.

Definition integerToRational : @SAWCoreScaffolding.Integer -> @Rational :=
  fun (x : @SAWCoreScaffolding.Integer) => @SAWCoreScaffolding.error (@Rational) "Unimplemented: fromInteger Rational"%string.

Definition seq_cong : forall (m : @Num), forall (n : @Num), forall (a : Type), forall (b : Type), @SAWCoreScaffolding.Eq (@Num) m n -> @SAWCoreScaffolding.Eq Type a b -> @SAWCoreScaffolding.Eq Type (@seq m a) (@seq n b) :=
  fun (m : @Num) (n : @Num) (a : Type) (b : Type) (eq_mn : @SAWCoreScaffolding.Eq (@Num) m n) (eq_ab : @SAWCoreScaffolding.Eq Type a b) => @SAWCorePrelude.trans Type (@seq m a) (@seq n a) (@seq n b) (@SAWCorePrelude.eq_cong (@Num) m n eq_mn Type (fun (x : @Num) => @seq x a)) (@SAWCorePrelude.eq_cong Type a b eq_ab Type (fun (x : Type) => @seq n x)).

Definition seq_cong1 : forall (m : @Num), forall (n : @Num), forall (a : Type), @SAWCoreScaffolding.Eq (@Num) m n -> @SAWCoreScaffolding.Eq Type (@seq m a) (@seq n a) :=
  fun (m : @Num) (n : @Num) (a : Type) (eq_mn : @SAWCoreScaffolding.Eq (@Num) m n) => @SAWCorePrelude.eq_cong (@Num) m n eq_mn Type (fun (x : @Num) => @seq x a).

Definition fun_cong : forall (a : Type), forall (b : Type), forall (c : Type), forall (d : Type), @SAWCoreScaffolding.Eq Type a b -> @SAWCoreScaffolding.Eq Type c d -> @SAWCoreScaffolding.Eq Type (a -> c) (b -> d) :=
  fun (a : Type) (b : Type) (c : Type) (d : Type) (eq_ab : @SAWCoreScaffolding.Eq Type a b) (eq_cd : @SAWCoreScaffolding.Eq Type c d) => @SAWCorePrelude.trans Type (a -> c) (b -> c) (b -> d) (@SAWCorePrelude.eq_cong Type a b eq_ab Type (fun (x : Type) => x -> c)) (@SAWCorePrelude.eq_cong Type c d eq_cd Type (fun (x : Type) => b -> x)).

Definition pair_cong : forall (a : Type), forall (a' : Type), forall (b : Type), forall (b' : Type), @SAWCoreScaffolding.Eq Type a a' -> @SAWCoreScaffolding.Eq Type b b' -> @SAWCoreScaffolding.Eq Type (prod a b) (prod a' b') :=
  fun (a : Type) (a' : Type) (b : Type) (b' : Type) (eq_a : @SAWCoreScaffolding.Eq Type a a') (eq_b : @SAWCoreScaffolding.Eq Type b b') => @SAWCorePrelude.trans Type (prod a b) (prod a' b) (prod a' b') (@SAWCorePrelude.eq_cong Type a a' eq_a Type (fun (x : Type) => prod x b)) (@SAWCorePrelude.eq_cong Type b b' eq_b Type (fun (x : Type) => prod a' x)).

Definition pair_cong1 : forall (a : Type), forall (a' : Type), forall (b : Type), @SAWCoreScaffolding.Eq Type a a' -> @SAWCoreScaffolding.Eq Type (prod a b) (prod a' b) :=
  fun (a : Type) (a' : Type) (b : Type) (eq_a : @SAWCoreScaffolding.Eq Type a a') => @SAWCorePrelude.eq_cong Type a a' eq_a Type (fun (x : Type) => prod x b).

Definition pair_cong2 : forall (a : Type), forall (b : Type), forall (b' : Type), @SAWCoreScaffolding.Eq Type b b' -> @SAWCoreScaffolding.Eq Type (prod a b) (prod a b') :=
  fun (a : Type) (b : Type) (b' : Type) (eq_b : @SAWCoreScaffolding.Eq Type b b') => @SAWCorePrelude.eq_cong Type b b' eq_b Type (fun (x : Type) => prod a x).

(* Cryptol.unsafeAssert_same_Num was skipped *)

Definition eListSel : forall (a : Type), forall (n : @Num), @seq n a -> @SAWCoreScaffolding.Nat -> a :=
  fun (a : Type) (n : @Num) => CryptolPrimitives.Num_rect (fun (num : @Num) => @seq num a -> @SAWCoreScaffolding.Nat -> a) (fun (n1 : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.sawAt n1 a) (@SAWCorePrelude.streamGet a) n.

Definition from : forall (a : Type), forall (b : Type), forall (m : @Num), forall (n : @Num), @seq m a -> (a -> @seq n b) -> @seq (@tcMul m n) (prod a b) :=
  fun (a : Type) (b : Type) (m : @Num) (n : @Num) => CryptolPrimitives.Num_rect (fun (m1 : @Num) => @seq m1 a -> (a -> @seq n b) -> @seq (@tcMul m1 n) (prod a b)) (fun (m1 : @SAWCoreScaffolding.Nat) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @SAWCoreVectorsAsCoqVectors.Vec m1 a -> (a -> @seq n1 b) -> @seq (@tcMul (@TCNum m1) n1) (prod a b)) (fun (n1 : @SAWCoreScaffolding.Nat) (xs : @SAWCoreVectorsAsCoqVectors.Vec m1 a) (k : a -> @SAWCoreVectorsAsCoqVectors.Vec n1 b) => @SAWCorePrelude.join m1 n1 (prod a b) (@SAWCorePrelude.map a (@SAWCoreVectorsAsCoqVectors.Vec n1 (prod a b)) (fun (x : a) => @SAWCorePrelude.map b (prod a b) (fun (y : b) => pair x y) n1 (k x)) m1 xs)) (@SAWCorePrelude.natCase (fun (m' : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.Vec m' a -> (a -> @SAWCorePrelude.Stream b) -> @seq (@SAWCorePrelude.if0Nat (@Num) m' (@TCNum 0) (@TCInf)) (prod a b)) (fun (xs : @SAWCoreVectorsAsCoqVectors.Vec 0 a) (k : a -> @SAWCorePrelude.Stream b) => @SAWCoreVectorsAsCoqVectors.EmptyVec (prod a b)) (fun (m' : @SAWCoreScaffolding.Nat) (xs : @SAWCoreVectorsAsCoqVectors.Vec (@SAWCoreScaffolding.Succ m') a) (k : a -> @SAWCorePrelude.Stream b) => (fun (x : a) => @SAWCorePrelude.streamMap b (prod a b) (fun (y : b) => pair x y) (k x)) (@SAWCorePrelude.sawAt (@SAWCoreScaffolding.Succ m') a xs 0)) m1) n) (CryptolPrimitives.Num_rect (fun (n1 : @Num) => @SAWCorePrelude.Stream a -> (a -> @seq n1 b) -> @seq (@tcMul (@TCInf) n1) (prod a b)) (fun (n1 : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.natCase (fun (n' : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.Stream a -> (a -> @SAWCoreVectorsAsCoqVectors.Vec n' b) -> @seq (@SAWCorePrelude.if0Nat (@Num) n' (@TCNum 0) (@TCInf)) (prod a b)) (fun (xs : @SAWCorePrelude.Stream a) (k : a -> @SAWCoreVectorsAsCoqVectors.Vec 0 b) => @SAWCoreVectorsAsCoqVectors.EmptyVec (prod a b)) (fun (n' : @SAWCoreScaffolding.Nat) (xs : @SAWCorePrelude.Stream a) (k : a -> @SAWCoreVectorsAsCoqVectors.Vec (@SAWCoreScaffolding.Succ n') b) => @SAWCorePrelude.streamJoin (prod a b) n' (@SAWCorePrelude.streamMap a (@SAWCoreVectorsAsCoqVectors.Vec (@SAWCoreScaffolding.Succ n') (prod a b)) (fun (x : a) => @SAWCorePrelude.map b (prod a b) (fun (y : b) => pair x y) (@SAWCoreScaffolding.Succ n') (k x)) xs)) n1) (fun (xs : @SAWCorePrelude.Stream a) (k : a -> @SAWCorePrelude.Stream b) => (fun (x : a) => @SAWCorePrelude.streamMap b (prod a b) (fun (y : b) => pair x y) (k x)) (@SAWCorePrelude.streamGet a xs 0)) n) m.

Definition mlet : forall (a : Type), forall (b : Type), forall (n : @Num), a -> (a -> @seq n b) -> @seq n (prod a b) :=
  fun (a : Type) (b : Type) (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => a -> (a -> @seq n1 b) -> @seq n1 (prod a b)) (fun (n1 : @SAWCoreScaffolding.Nat) (x : a) (f : a -> @SAWCoreVectorsAsCoqVectors.Vec n1 b) => @SAWCorePrelude.map b (prod a b) (fun (y : b) => pair x y) n1 (f x)) (fun (x : a) (f : a -> @SAWCorePrelude.Stream b) => @SAWCorePrelude.streamMap b (prod a b) (fun (y : b) => pair x y) (f x)) n.

Definition seqZip : forall (a : Type), forall (b : Type), forall (m : @Num), forall (n : @Num), @seq m a -> @seq n b -> @seq (@tcMin m n) (prod a b) :=
  fun (a : Type) (b : Type) (m : @Num) (n : @Num) => CryptolPrimitives.Num_rect (fun (m1 : @Num) => @seq m1 a -> @seq n b -> @seq (@tcMin m1 n) (prod a b)) (fun (m1 : @SAWCoreScaffolding.Nat) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @SAWCoreVectorsAsCoqVectors.Vec m1 a -> @seq n1 b -> @seq (@tcMin (@TCNum m1) n1) (prod a b)) (fun (n1 : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.zip a b m1 n1) (fun (xs : @SAWCoreVectorsAsCoqVectors.Vec m1 a) (ys : @SAWCorePrelude.Stream b) => @SAWCoreVectorsAsCoqVectors.gen m1 (prod a b) (fun (i : @SAWCoreScaffolding.Nat) => pair (@SAWCorePrelude.sawAt m1 a xs i) (@SAWCorePrelude.streamGet b ys i))) n) (CryptolPrimitives.Num_rect (fun (n1 : @Num) => @SAWCorePrelude.Stream a -> @seq n1 b -> @seq (@tcMin (@TCInf) n1) (prod a b)) (fun (n1 : @SAWCoreScaffolding.Nat) (xs : @SAWCorePrelude.Stream a) (ys : @SAWCoreVectorsAsCoqVectors.Vec n1 b) => @SAWCoreVectorsAsCoqVectors.gen n1 (prod a b) (fun (i : @SAWCoreScaffolding.Nat) => pair (@SAWCorePrelude.streamGet a xs i) (@SAWCorePrelude.sawAt n1 b ys i))) (@SAWCorePrelude.streamMap2 a b (prod a b) (fun (x : a) (y : b) => pair x y)) n) m.

Definition seqBinary : forall (n : @Num), forall (a : Type), (a -> a -> a) -> @seq n a -> @seq n a -> @seq n a :=
  fun (num : @Num) (a : Type) (f : a -> a -> a) => CryptolPrimitives.Num_rect (fun (n : @Num) => @seq n a -> @seq n a -> @seq n a) (fun (n : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.zipWith a a a f n) (@SAWCorePrelude.streamMap2 a a a f) num.

Definition unitUnary : unit -> unit :=
  fun (_1 : unit) => tt.

Definition unitBinary : unit -> unit -> unit :=
  fun (_1 : unit) (_2 : unit) => tt.

Definition pairUnary : forall (a : Type), forall (b : Type), (a -> a) -> (b -> b) -> prod a b -> prod a b :=
  fun (a : Type) (b : Type) (f : a -> a) (g : b -> b) (xy : prod a b) => pair (f (@SAWCoreScaffolding.fst a b xy)) (g (@SAWCoreScaffolding.snd a b xy)).

Definition pairBinary : forall (a : Type), forall (b : Type), (a -> a -> a) -> (b -> b -> b) -> prod a b -> prod a b -> prod a b :=
  fun (a : Type) (b : Type) (f : a -> a -> a) (g : b -> b -> b) (x12 : prod a b) (y12 : prod a b) => pair (f (@SAWCoreScaffolding.fst a b x12) (@SAWCoreScaffolding.fst a b y12)) (g (@SAWCoreScaffolding.snd a b x12) (@SAWCoreScaffolding.snd a b y12)).

Definition funBinary : forall (a : Type), forall (b : Type), (b -> b -> b) -> (a -> b) -> (a -> b) -> a -> b :=
  fun (a : Type) (b : Type) (op : b -> b -> b) (f : a -> b) (g : a -> b) (x : a) => op (f x) (g x).

Definition errorUnary : forall (s : @SAWCoreScaffolding.String), forall (a : Type), a -> a :=
  fun (s : @SAWCoreScaffolding.String) (a : Type) (_1 : a) => @SAWCoreScaffolding.error a s.

Definition errorBinary : forall (s : @SAWCoreScaffolding.String), forall (a : Type), a -> a -> a :=
  fun (s : @SAWCoreScaffolding.String) (a : Type) (_1 : a) (_2 : a) => @SAWCoreScaffolding.error a s.

Definition boolCmp : @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool :=
  fun (x : @SAWCoreScaffolding.Bool) (y : @SAWCoreScaffolding.Bool) (k : @SAWCoreScaffolding.Bool) => if x then @SAWCoreScaffolding.and y k else @SAWCoreScaffolding.or y k.

Definition integerCmp : @SAWCoreScaffolding.Integer -> @SAWCoreScaffolding.Integer -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool :=
  fun (x : @SAWCoreScaffolding.Integer) (y : @SAWCoreScaffolding.Integer) (k : @SAWCoreScaffolding.Bool) => @SAWCoreScaffolding.or (@SAWCoreScaffolding.intLt x y) (@SAWCoreScaffolding.and (@SAWCoreScaffolding.intEq x y) k).

Definition rationalCmp : @Rational -> @Rational -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool :=
  fun (x : unit) (y : unit) (k : @SAWCoreScaffolding.Bool) => @SAWCoreScaffolding.or (@ltRational x y) (@SAWCoreScaffolding.and (@eqRational x y) k).

Definition bvCmp : forall (n : @SAWCoreScaffolding.Nat), @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool :=
  fun (n : @SAWCoreScaffolding.Nat) (x : @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) (y : @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) (k : @SAWCoreScaffolding.Bool) => @SAWCoreScaffolding.or (@SAWCoreVectorsAsCoqVectors.bvult n x y) (@SAWCoreScaffolding.and (@SAWCorePrelude.bvEq n x y) k).

Definition bvSCmp : forall (n : @SAWCoreScaffolding.Nat), @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool :=
  fun (n : @SAWCoreScaffolding.Nat) (x : @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) (y : @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) (k : @SAWCoreScaffolding.Bool) => @SAWCoreScaffolding.or (@SAWCoreVectorsAsCoqVectors.bvslt n x y) (@SAWCoreScaffolding.and (@SAWCorePrelude.bvEq n x y) k).

Definition vecCmp : forall (n : @SAWCoreScaffolding.Nat), forall (a : Type), (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n a -> @SAWCoreVectorsAsCoqVectors.Vec n a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool :=
  fun (n : @SAWCoreScaffolding.Nat) (a : Type) (f : a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (xs : @SAWCoreVectorsAsCoqVectors.Vec n a) (ys : @SAWCoreVectorsAsCoqVectors.Vec n a) (k : @SAWCoreScaffolding.Bool) => @SAWCoreVectorsAsCoqVectors.foldr (@SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.Bool) n (fun (f1 : @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) => f1) k (@SAWCorePrelude.zipWith a a (@SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) f n xs ys).

Definition unitCmp : unit -> unit -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool :=
  fun (_1 : unit) (_2 : unit) (_3 : @SAWCoreScaffolding.Bool) => @SAWCoreScaffolding.false.

Definition pairEq : forall (a : Type), forall (b : Type), (a -> a -> @SAWCoreScaffolding.Bool) -> (b -> b -> @SAWCoreScaffolding.Bool) -> prod a b -> prod a b -> @SAWCoreScaffolding.Bool :=
  fun (a : Type) (b : Type) (f : a -> a -> @SAWCoreScaffolding.Bool) (g : b -> b -> @SAWCoreScaffolding.Bool) (x : prod a b) (y : prod a b) => @SAWCoreScaffolding.and (f (@SAWCoreScaffolding.fst a b x) (@SAWCoreScaffolding.fst a b y)) (g (@SAWCoreScaffolding.snd a b x) (@SAWCoreScaffolding.snd a b y)).

Definition pairCmp : forall (a : Type), forall (b : Type), (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) -> (b -> b -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) -> prod a b -> prod a b -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool :=
  fun (a : Type) (b : Type) (f : a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (g : b -> b -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (x12 : prod a b) (y12 : prod a b) (k : @SAWCoreScaffolding.Bool) => f (@SAWCoreScaffolding.fst a b x12) (@SAWCoreScaffolding.fst a b y12) (g (@SAWCoreScaffolding.snd a b x12) (@SAWCoreScaffolding.snd a b y12) k).

Definition PEq : Type -> Type :=
  fun (a : Type) => RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil.

Definition PEqBit : @PEq (@SAWCoreScaffolding.Bool) :=
  RecordCons "eq" (@SAWCoreScaffolding.boolEq) RecordNil.

Definition PEqInteger : @PEq (@SAWCoreScaffolding.Integer) :=
  RecordCons "eq" (@SAWCoreScaffolding.intEq) RecordNil.

Definition PEqRational : @PEq (@Rational) :=
  RecordCons "eq" (@eqRational) RecordNil.

Definition PEqIntMod : forall (n : @SAWCoreScaffolding.Nat), @PEq (@SAWCoreScaffolding.IntMod n) :=
  fun (n : @SAWCoreScaffolding.Nat) => RecordCons "eq" (@SAWCoreScaffolding.intModEq n) RecordNil.

Definition PEqIntModNum : forall (num : @Num), @PEq (@IntModNum num) :=
  fun (num : @Num) => CryptolPrimitives.Num_rect (fun (n : @Num) => @PEq (@IntModNum n)) (@PEqIntMod) (@PEqInteger) num.

Definition PEqVec : forall (n : @SAWCoreScaffolding.Nat), forall (a : Type), @PEq a -> @PEq (@SAWCoreVectorsAsCoqVectors.Vec n a) :=
  fun (n : @SAWCoreScaffolding.Nat) (a : Type) (pa : RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) => RecordCons "eq" (@SAWCorePrelude.vecEq n a (RecordProj pa "eq")) RecordNil.

Definition PEqSeq : forall (n : @Num), forall (a : Type), @PEq a -> @PEq (@seq n a) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => forall (a : Type), @PEq a -> @PEq (@seq n1 a)) (fun (n1 : @SAWCoreScaffolding.Nat) => @PEqVec n1) (fun (a : Type) (pa : RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) => @SAWCoreScaffolding.error (@PEq (@SAWCorePrelude.Stream a)) "invalid Eq instance"%string) n.

Definition PEqWord : forall (n : @SAWCoreScaffolding.Nat), @PEq (@SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @SAWCoreScaffolding.Nat) => RecordCons "eq" (@SAWCorePrelude.bvEq n) RecordNil.

Definition PEqSeqBool : forall (n : @Num), @PEq (@seq n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @PEq (@seq n1 (@SAWCoreScaffolding.Bool))) (fun (n1 : @SAWCoreScaffolding.Nat) => @PEqWord n1) (@SAWCoreScaffolding.error (@PEq (@SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool))) "invalid Eq instance"%string) n.

Definition PEqUnit : @PEq unit :=
  RecordCons "eq" (fun (x : unit) (y : unit) => @SAWCoreScaffolding.true) RecordNil.

Definition PEqPair : forall (a : Type), forall (b : Type), @PEq a -> @PEq b -> @PEq (prod a b) :=
  fun (a : Type) (b : Type) (pa : RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) (pb : RecordTypeCons "eq" (b -> b -> @SAWCoreScaffolding.Bool) RecordTypeNil) => RecordCons "eq" (@pairEq a b (RecordProj pa "eq") (RecordProj pb "eq")) RecordNil.

Definition PCmp : Type -> Type :=
  fun (a : Type) => RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (@PEq a) RecordTypeNil).

Definition PCmpBit : @PCmp (@SAWCoreScaffolding.Bool) :=
  RecordCons "cmp" (@boolCmp) (RecordCons "cmpEq" (@PEqBit) RecordNil).

Definition PCmpInteger : @PCmp (@SAWCoreScaffolding.Integer) :=
  RecordCons "cmp" (@integerCmp) (RecordCons "cmpEq" (@PEqInteger) RecordNil).

Definition PCmpRational : @PCmp (@Rational) :=
  RecordCons "cmp" (@rationalCmp) (RecordCons "cmpEq" (@PEqRational) RecordNil).

Definition PCmpVec : forall (n : @SAWCoreScaffolding.Nat), forall (a : Type), @PCmp a -> @PCmp (@SAWCoreVectorsAsCoqVectors.Vec n a) :=
  fun (n : @SAWCoreScaffolding.Nat) (a : Type) (pa : RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) => RecordCons "cmp" (@vecCmp n a (RecordProj pa "cmp")) (RecordCons "cmpEq" (@PEqVec n a (RecordProj pa "cmpEq")) RecordNil).

Definition PCmpSeq : forall (n : @Num), forall (a : Type), @PCmp a -> @PCmp (@seq n a) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => forall (a : Type), @PCmp a -> @PCmp (@seq n1 a)) (fun (n1 : @SAWCoreScaffolding.Nat) => @PCmpVec n1) (fun (a : Type) (pa : RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) => @SAWCoreScaffolding.error (@PCmp (@SAWCorePrelude.Stream a)) "invalid Cmp instance"%string) n.

Definition PCmpWord : forall (n : @SAWCoreScaffolding.Nat), @PCmp (@SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @SAWCoreScaffolding.Nat) => RecordCons "cmp" (@bvCmp n) (RecordCons "cmpEq" (@PEqWord n) RecordNil).

Definition PCmpSeqBool : forall (n : @Num), @PCmp (@seq n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @PCmp (@seq n1 (@SAWCoreScaffolding.Bool))) (fun (n1 : @SAWCoreScaffolding.Nat) => @PCmpWord n1) (@SAWCoreScaffolding.error (@PCmp (@SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool))) "invalid Cmp instance"%string) n.

Definition PCmpUnit : @PCmp unit :=
  RecordCons "cmp" (@unitCmp) (RecordCons "cmpEq" (@PEqUnit) RecordNil).

Definition PCmpPair : forall (a : Type), forall (b : Type), @PCmp a -> @PCmp b -> @PCmp (prod a b) :=
  fun (a : Type) (b : Type) (pa : RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (pb : RecordTypeCons "cmp" (b -> b -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (b -> b -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) => RecordCons "cmp" (@pairCmp a b (RecordProj pa "cmp") (RecordProj pb "cmp")) (RecordCons "cmpEq" (@PEqPair a b (RecordProj pa "cmpEq") (RecordProj pb "cmpEq")) RecordNil).

Definition PSignedCmp : Type -> Type :=
  fun (a : Type) => RecordTypeCons "scmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "signedCmpEq" (@PEq a) RecordTypeNil).

Definition PSignedCmpVec : forall (n : @SAWCoreScaffolding.Nat), forall (a : Type), @PSignedCmp a -> @PSignedCmp (@SAWCoreVectorsAsCoqVectors.Vec n a) :=
  fun (n : @SAWCoreScaffolding.Nat) (a : Type) (pa : RecordTypeCons "scmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "signedCmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) => RecordCons "scmp" (@vecCmp n a (RecordProj pa "scmp")) (RecordCons "signedCmpEq" (@PEqVec n a (RecordProj pa "signedCmpEq")) RecordNil).

Definition PSignedCmpSeq : forall (n : @Num), forall (a : Type), @PSignedCmp a -> @PSignedCmp (@seq n a) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => forall (a : Type), @PSignedCmp a -> @PSignedCmp (@seq n1 a)) (fun (n1 : @SAWCoreScaffolding.Nat) => @PSignedCmpVec n1) (fun (a : Type) (pa : RecordTypeCons "scmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "signedCmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) => @SAWCoreScaffolding.error (@PSignedCmp (@SAWCorePrelude.Stream a)) "invalid SignedCmp instance"%string) n.

Definition PSignedCmpWord : forall (n : @SAWCoreScaffolding.Nat), @PSignedCmp (@SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @SAWCoreScaffolding.Nat) => RecordCons "scmp" (@bvSCmp n) (RecordCons "signedCmpEq" (@PEqWord n) RecordNil).

Definition PSignedCmpSeqBool : forall (n : @Num), @PSignedCmp (@seq n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @PSignedCmp (@seq n1 (@SAWCoreScaffolding.Bool))) (fun (n1 : @SAWCoreScaffolding.Nat) => @PSignedCmpWord n1) (@SAWCoreScaffolding.error (@PSignedCmp (@SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool))) "invalid SignedCmp instance"%string) n.

Definition PSignedCmpUnit : @PSignedCmp unit :=
  RecordCons "scmp" (@unitCmp) (RecordCons "signedCmpEq" (@PEqUnit) RecordNil).

Definition PSignedCmpPair : forall (a : Type), forall (b : Type), @PSignedCmp a -> @PSignedCmp b -> @PSignedCmp (prod a b) :=
  fun (a : Type) (b : Type) (pa : RecordTypeCons "scmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "signedCmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (pb : RecordTypeCons "scmp" (b -> b -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "signedCmpEq" (RecordTypeCons "eq" (b -> b -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) => RecordCons "scmp" (@pairCmp a b (RecordProj pa "scmp") (RecordProj pb "scmp")) (RecordCons "signedCmpEq" (@PEqPair a b (RecordProj pa "signedCmpEq") (RecordProj pb "signedCmpEq")) RecordNil).

Definition PZero : Type -> Type :=
  fun (a : Type) => a.

Definition PZeroBit : @PZero (@SAWCoreScaffolding.Bool) :=
  @SAWCoreScaffolding.false.

Definition PZeroInteger : @PZero (@SAWCoreScaffolding.Integer) :=
  0%Z.

Definition PZeroIntMod : forall (n : @SAWCoreScaffolding.Nat), @PZero (@SAWCoreScaffolding.IntMod n) :=
  fun (n : @SAWCoreScaffolding.Nat) => @SAWCoreScaffolding.toIntMod n 0%Z.

Definition PZeroRational : @PZero (@Rational) :=
  @integerToRational 0%Z.

Definition PZeroIntModNum : forall (num : @Num), @PZero (@IntModNum num) :=
  fun (num : @Num) => CryptolPrimitives.Num_rect (fun (n : @Num) => @PZero (@IntModNum n)) (@PZeroIntMod) (@PZeroInteger) num.

Definition PZeroSeq : forall (n : @Num), forall (a : Type), @PZero a -> @PZero (@seq n a) :=
  fun (n : @Num) (a : Type) (pa : a) => @seqConst n a pa.

Definition PZeroSeqBool : forall (n : @Num), @PZero (@seq n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @PZero (@seq n1 (@SAWCoreScaffolding.Bool))) (fun (n1 : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.bvNat n1 0) (@SAWCorePrelude.streamConst (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.false)) n.

Definition PZeroFun : forall (a : Type), forall (b : Type), @PZero b -> @PZero (a -> b) :=
  fun (a : Type) (b : Type) (pb : b) (_1 : a) => pb.

Definition PLogic : Type -> Type :=
  fun (a : Type) => RecordTypeCons "and" (a -> a -> a) (RecordTypeCons "logicZero" (@PZero a) (RecordTypeCons "not" (a -> a) (RecordTypeCons "or" (a -> a -> a) (RecordTypeCons "xor" (a -> a -> a) RecordTypeNil)))).

Definition PLogicBit : @PLogic (@SAWCoreScaffolding.Bool) :=
  RecordCons "and" (@SAWCoreScaffolding.and) (RecordCons "logicZero" (@PZeroBit) (RecordCons "not" (@SAWCoreScaffolding.not) (RecordCons "or" (@SAWCoreScaffolding.or) (RecordCons "xor" (@SAWCoreScaffolding.xor) RecordNil)))).

Definition PLogicVec : forall (n : @SAWCoreScaffolding.Nat), forall (a : Type), @PLogic a -> @PLogic (@SAWCoreVectorsAsCoqVectors.Vec n a) :=
  fun (n : @SAWCoreScaffolding.Nat) (a : Type) (pa : RecordTypeCons "and" (a -> a -> a) (RecordTypeCons "logicZero" a (RecordTypeCons "not" (a -> a) (RecordTypeCons "or" (a -> a -> a) (RecordTypeCons "xor" (a -> a -> a) RecordTypeNil))))) => RecordCons "and" (@SAWCorePrelude.zipWith a a a (RecordProj pa "and") n) (RecordCons "logicZero" (@SAWCorePrelude.replicate n a (RecordProj pa "logicZero")) (RecordCons "not" (@SAWCorePrelude.map a a (RecordProj pa "not") n) (RecordCons "or" (@SAWCorePrelude.zipWith a a a (RecordProj pa "or") n) (RecordCons "xor" (@SAWCorePrelude.zipWith a a a (RecordProj pa "xor") n) RecordNil)))).

Definition PLogicStream : forall (a : Type), @PLogic a -> @PLogic (@SAWCorePrelude.Stream a) :=
  fun (a : Type) (pa : RecordTypeCons "and" (a -> a -> a) (RecordTypeCons "logicZero" a (RecordTypeCons "not" (a -> a) (RecordTypeCons "or" (a -> a -> a) (RecordTypeCons "xor" (a -> a -> a) RecordTypeNil))))) => RecordCons "and" (@SAWCorePrelude.streamMap2 a a a (RecordProj pa "and")) (RecordCons "logicZero" (@SAWCorePrelude.streamConst a (RecordProj pa "logicZero")) (RecordCons "not" (@SAWCorePrelude.streamMap a a (RecordProj pa "not")) (RecordCons "or" (@SAWCorePrelude.streamMap2 a a a (RecordProj pa "or")) (RecordCons "xor" (@SAWCorePrelude.streamMap2 a a a (RecordProj pa "xor")) RecordNil)))).

Definition PLogicSeq : forall (n : @Num), forall (a : Type), @PLogic a -> @PLogic (@seq n a) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => forall (a : Type), @PLogic a -> @PLogic (@seq n1 a)) (fun (n1 : @SAWCoreScaffolding.Nat) => @PLogicVec n1) (@PLogicStream) n.

Definition PLogicWord : forall (n : @SAWCoreScaffolding.Nat), @PLogic (@SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @SAWCoreScaffolding.Nat) => RecordCons "and" (@SAWCorePrelude.bvAnd n) (RecordCons "logicZero" (@SAWCoreVectorsAsCoqVectors.bvNat n 0) (RecordCons "not" (@SAWCorePrelude.bvNot n) (RecordCons "or" (@SAWCorePrelude.bvOr n) (RecordCons "xor" (@SAWCorePrelude.bvXor n) RecordNil)))).

Definition PLogicSeqBool : forall (n : @Num), @PLogic (@seq n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @PLogic (@seq n1 (@SAWCoreScaffolding.Bool))) (fun (n1 : @SAWCoreScaffolding.Nat) => @PLogicWord n1) (@PLogicStream (@SAWCoreScaffolding.Bool) (@PLogicBit)) n.

Definition PLogicFun : forall (a : Type), forall (b : Type), @PLogic b -> @PLogic (a -> b) :=
  fun (a : Type) (b : Type) (pb : RecordTypeCons "and" (b -> b -> b) (RecordTypeCons "logicZero" b (RecordTypeCons "not" (b -> b) (RecordTypeCons "or" (b -> b -> b) (RecordTypeCons "xor" (b -> b -> b) RecordTypeNil))))) => RecordCons "and" (@funBinary a b (RecordProj pb "and")) (RecordCons "logicZero" (@PZeroFun a b (RecordProj pb "logicZero")) (RecordCons "not" (@compose a b b (RecordProj pb "not")) (RecordCons "or" (@funBinary a b (RecordProj pb "or")) (RecordCons "xor" (@funBinary a b (RecordProj pb "xor")) RecordNil)))).

Definition PLogicUnit : @PLogic unit :=
  RecordCons "and" (@unitBinary) (RecordCons "logicZero" tt (RecordCons "not" (@unitUnary) (RecordCons "or" (@unitBinary) (RecordCons "xor" (@unitBinary) RecordNil)))).

Definition PLogicPair : forall (a : Type), forall (b : Type), @PLogic a -> @PLogic b -> @PLogic (prod a b) :=
  fun (a : Type) (b : Type) (pa : RecordTypeCons "and" (a -> a -> a) (RecordTypeCons "logicZero" a (RecordTypeCons "not" (a -> a) (RecordTypeCons "or" (a -> a -> a) (RecordTypeCons "xor" (a -> a -> a) RecordTypeNil))))) (pb : RecordTypeCons "and" (b -> b -> b) (RecordTypeCons "logicZero" b (RecordTypeCons "not" (b -> b) (RecordTypeCons "or" (b -> b -> b) (RecordTypeCons "xor" (b -> b -> b) RecordTypeNil))))) => RecordCons "and" (@pairBinary a b (RecordProj pa "and") (RecordProj pb "and")) (RecordCons "logicZero" (pair (RecordProj pa "logicZero") (RecordProj pb "logicZero")) (RecordCons "not" (@pairUnary a b (RecordProj pa "not") (RecordProj pb "not")) (RecordCons "or" (@pairBinary a b (RecordProj pa "or") (RecordProj pb "or")) (RecordCons "xor" (@pairBinary a b (RecordProj pa "xor") (RecordProj pb "xor")) RecordNil)))).

Definition PRing : Type -> Type :=
  fun (a : Type) => RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" (@PZero a) (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil))))).

Definition PRingInteger : @PRing (@SAWCoreScaffolding.Integer) :=
  RecordCons "add" (@SAWCoreScaffolding.intAdd) (RecordCons "int" (fun (i : @SAWCoreScaffolding.Integer) => i) (RecordCons "mul" (@SAWCoreScaffolding.intMul) (RecordCons "neg" (@SAWCoreScaffolding.intNeg) (RecordCons "ringZero" (@PZeroInteger) (RecordCons "sub" (@SAWCoreScaffolding.intSub) RecordNil))))).

Definition PRingIntMod : forall (n : @SAWCoreScaffolding.Nat), @PRing (@SAWCoreScaffolding.IntMod n) :=
  fun (n : @SAWCoreScaffolding.Nat) => RecordCons "add" (@SAWCoreScaffolding.intModAdd n) (RecordCons "int" (@SAWCoreScaffolding.toIntMod n) (RecordCons "mul" (@SAWCoreScaffolding.intModMul n) (RecordCons "neg" (@SAWCoreScaffolding.intModNeg n) (RecordCons "ringZero" (@PZeroIntMod n) (RecordCons "sub" (@SAWCoreScaffolding.intModSub n) RecordNil))))).

Definition PRingIntModNum : forall (num : @Num), @PRing (@IntModNum num) :=
  fun (num : @Num) => CryptolPrimitives.Num_rect (fun (n : @Num) => @PRing (@IntModNum n)) (@PRingIntMod) (@PRingInteger) num.

Definition PRingRational : @PRing (@Rational) :=
  RecordCons "add" (@addRational) (RecordCons "int" (@integerToRational) (RecordCons "mul" (@mulRational) (RecordCons "neg" (@negRational) (RecordCons "ringZero" (@PZeroRational) (RecordCons "sub" (@subRational) RecordNil))))).

Definition PRingVec : forall (n : @SAWCoreScaffolding.Nat), forall (a : Type), @PRing a -> @PRing (@SAWCoreVectorsAsCoqVectors.Vec n a) :=
  fun (n : @SAWCoreScaffolding.Nat) (a : Type) (pa : RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) => RecordCons "add" (@SAWCorePrelude.zipWith a a a (RecordProj pa "add") n) (RecordCons "int" (fun (i : @SAWCoreScaffolding.Integer) => @SAWCorePrelude.replicate n a (RecordProj pa "int" i)) (RecordCons "mul" (@SAWCorePrelude.zipWith a a a (RecordProj pa "mul") n) (RecordCons "neg" (@SAWCorePrelude.map a a (RecordProj pa "neg") n) (RecordCons "ringZero" (@SAWCorePrelude.replicate n a (RecordProj pa "ringZero")) (RecordCons "sub" (@SAWCorePrelude.zipWith a a a (RecordProj pa "sub") n) RecordNil))))).

Definition PRingStream : forall (a : Type), @PRing a -> @PRing (@SAWCorePrelude.Stream a) :=
  fun (a : Type) (pa : RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) => RecordCons "add" (@SAWCorePrelude.streamMap2 a a a (RecordProj pa "add")) (RecordCons "int" (fun (i : @SAWCoreScaffolding.Integer) => @SAWCorePrelude.streamConst a (RecordProj pa "int" i)) (RecordCons "mul" (@SAWCorePrelude.streamMap2 a a a (RecordProj pa "mul")) (RecordCons "neg" (@SAWCorePrelude.streamMap a a (RecordProj pa "neg")) (RecordCons "ringZero" (@SAWCorePrelude.streamConst a (RecordProj pa "ringZero")) (RecordCons "sub" (@SAWCorePrelude.streamMap2 a a a (RecordProj pa "sub")) RecordNil))))).

Definition PRingSeq : forall (n : @Num), forall (a : Type), @PRing a -> @PRing (@seq n a) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => forall (a : Type), @PRing a -> @PRing (@seq n1 a)) (fun (n1 : @SAWCoreScaffolding.Nat) => @PRingVec n1) (@PRingStream) n.

Definition PRingWord : forall (n : @SAWCoreScaffolding.Nat), @PRing (@SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @SAWCoreScaffolding.Nat) => RecordCons "add" (@SAWCoreVectorsAsCoqVectors.bvAdd n) (RecordCons "int" (@SAWCoreVectorsAsCoqVectors.intToBv n) (RecordCons "mul" (@SAWCoreVectorsAsCoqVectors.bvMul n) (RecordCons "neg" (@SAWCoreVectorsAsCoqVectors.bvNeg n) (RecordCons "ringZero" (@SAWCoreVectorsAsCoqVectors.bvNat n 0) (RecordCons "sub" (@SAWCoreVectorsAsCoqVectors.bvSub n) RecordNil))))).

Definition PRingSeqBool : forall (n : @Num), @PRing (@seq n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @PRing (@seq n1 (@SAWCoreScaffolding.Bool))) (fun (n1 : @SAWCoreScaffolding.Nat) => @PRingWord n1) (@SAWCoreScaffolding.error (@PRing (@SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool))) "PRingSeqBool: no instance for streams"%string) n.

Definition PRingFun : forall (a : Type), forall (b : Type), @PRing b -> @PRing (a -> b) :=
  fun (a : Type) (b : Type) (pb : RecordTypeCons "add" (b -> b -> b) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> b) (RecordTypeCons "mul" (b -> b -> b) (RecordTypeCons "neg" (b -> b) (RecordTypeCons "ringZero" b (RecordTypeCons "sub" (b -> b -> b) RecordTypeNil)))))) => RecordCons "add" (@funBinary a b (RecordProj pb "add")) (RecordCons "int" (fun (i : @SAWCoreScaffolding.Integer) (_1 : a) => RecordProj pb "int" i) (RecordCons "mul" (@funBinary a b (RecordProj pb "mul")) (RecordCons "neg" (@compose a b b (RecordProj pb "neg")) (RecordCons "ringZero" (@PZeroFun a b (RecordProj pb "ringZero")) (RecordCons "sub" (@funBinary a b (RecordProj pb "sub")) RecordNil))))).

Definition PRingUnit : @PRing unit :=
  RecordCons "add" (@unitBinary) (RecordCons "int" (fun (i : @SAWCoreScaffolding.Integer) => tt) (RecordCons "mul" (@unitBinary) (RecordCons "neg" (@unitUnary) (RecordCons "ringZero" tt (RecordCons "sub" (@unitBinary) RecordNil))))).

Definition PRingPair : forall (a : Type), forall (b : Type), @PRing a -> @PRing b -> @PRing (prod a b) :=
  fun (a : Type) (b : Type) (pa : RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (pb : RecordTypeCons "add" (b -> b -> b) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> b) (RecordTypeCons "mul" (b -> b -> b) (RecordTypeCons "neg" (b -> b) (RecordTypeCons "ringZero" b (RecordTypeCons "sub" (b -> b -> b) RecordTypeNil)))))) => RecordCons "add" (@pairBinary a b (RecordProj pa "add") (RecordProj pb "add")) (RecordCons "int" (fun (i : @SAWCoreScaffolding.Integer) => pair (RecordProj pa "int" i) (RecordProj pb "int" i)) (RecordCons "mul" (@pairBinary a b (RecordProj pa "mul") (RecordProj pb "mul")) (RecordCons "neg" (@pairUnary a b (RecordProj pa "neg") (RecordProj pb "neg")) (RecordCons "ringZero" (pair (RecordProj pa "ringZero") (RecordProj pb "ringZero")) (RecordCons "sub" (@pairBinary a b (RecordProj pa "sub") (RecordProj pb "sub")) RecordNil))))).

Definition PIntegral : Type -> Type :=
  fun (a : Type) => RecordTypeCons "div" (a -> a -> a) (RecordTypeCons "integralRing" (@PRing a) (RecordTypeCons "mod" (a -> a -> a) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> a -> r) (RecordTypeCons "toInt" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil)))).

Definition PIntegralInteger : @PIntegral (@SAWCoreScaffolding.Integer) :=
  RecordCons "div" (@SAWCoreScaffolding.intDiv) (RecordCons "integralRing" (@PRingInteger) (RecordCons "mod" (@SAWCoreScaffolding.intMod) (RecordCons "posNegCases" (fun (r : Type) (pos : @SAWCoreScaffolding.Nat -> r) (neg : @SAWCoreScaffolding.Nat -> r) (i : @SAWCoreScaffolding.Integer) => if @SAWCoreScaffolding.intLe 0%Z i then pos (@SAWCoreScaffolding.intToNat i) else neg (@SAWCoreScaffolding.intToNat (@SAWCoreScaffolding.intNeg i))) (RecordCons "toInt" (fun (i : @SAWCoreScaffolding.Integer) => i) RecordNil)))).

Definition PIntegralWord : forall (n : @SAWCoreScaffolding.Nat), @PIntegral (@SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @SAWCoreScaffolding.Nat) => RecordCons "div" (@SAWCoreVectorsAsCoqVectors.bvUDiv n) (RecordCons "integralRing" (@PRingWord n) (RecordCons "mod" (@SAWCoreVectorsAsCoqVectors.bvURem n) (RecordCons "posNegCases" (fun (r : Type) (pos : @SAWCoreScaffolding.Nat -> r) (neg : @SAWCoreScaffolding.Nat -> r) (i : @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) => pos (@SAWCoreVectorsAsCoqVectors.bvToNat n i)) (RecordCons "toInt" (@SAWCoreVectorsAsCoqVectors.bvToInt n) RecordNil)))).

Definition PIntegralSeqBool : forall (n : @Num), @PIntegral (@seq n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @PIntegral (@seq n1 (@SAWCoreScaffolding.Bool))) (fun (n1 : @SAWCoreScaffolding.Nat) => @PIntegralWord n1) (@SAWCoreScaffolding.error (@PIntegral (@SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool))) "PIntegralSeqBool: no instance for streams"%string) n.

Definition PField : Type -> Type :=
  fun (a : Type) => RecordTypeCons "fieldDiv" (a -> a -> a) (RecordTypeCons "fieldRing" (@PRing a) (RecordTypeCons "recip" (a -> a) RecordTypeNil)).

Definition PFieldRational : @PField (@Rational) :=
  RecordCons "fieldDiv" (fun (x : unit) (y : unit) => @SAWCoreScaffolding.error (@Rational) "Unimplemented: (/.) Rational"%string) (RecordCons "fieldRing" (@PRingRational) (RecordCons "recip" (fun (x : unit) => @SAWCoreScaffolding.error (@Rational) "Unimplemented: recip Rational"%string) RecordNil)).

Definition PFieldIntMod : forall (n : @SAWCoreScaffolding.Nat), @PField (@SAWCoreScaffolding.IntMod n) :=
  fun (n : @SAWCoreScaffolding.Nat) => RecordCons "fieldDiv" (fun (x : @SAWCoreScaffolding.IntMod n) (y : @SAWCoreScaffolding.IntMod n) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.IntMod n) "Unimplemented: (/.) IntMod"%string) (RecordCons "fieldRing" (@PRingIntMod n) (RecordCons "recip" (fun (x : @SAWCoreScaffolding.IntMod n) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.IntMod n) "Unimplemented: recip IntMod"%string) RecordNil)).

Definition PFieldIntModNum : forall (n : @Num), @PField (@IntModNum n) :=
  fun (num : @Num) => CryptolPrimitives.Num_rect (fun (n : @Num) => @PField (@IntModNum n)) (@PFieldIntMod) (@SAWCoreScaffolding.error (@PField (@IntModNum (@TCInf))) "PFieldIntModNum: no instance for inf"%string) num.

Definition PRound : Type -> Type :=
  fun (a : Type) => RecordTypeCons "ceiling" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "floor" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundAway" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundCmp" (@PCmp a) (RecordTypeCons "roundField" (@PField a) (RecordTypeCons "roundToEven" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "trunc" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil)))))).

Definition PRoundRational : @PRound (@Rational) :=
  RecordCons "ceiling" (fun (x : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Integer) "Unimplemented: ceiling Rational"%string) (RecordCons "floor" (fun (x : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Integer) "Unimplemented: floor Rational"%string) (RecordCons "roundAway" (fun (x : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Integer) "Unimplemented: roundAway Rational"%string) (RecordCons "roundCmp" (@PCmpRational) (RecordCons "roundField" (@PFieldRational) (RecordCons "roundToEven" (fun (x : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Integer) "Unimplemented: roundToEven Rational"%string) (RecordCons "trunc" (fun (x : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Integer) "Unimplemented: trunc Rational"%string) RecordNil)))))).

Definition PLiteral : forall (a : Type), Type :=
  fun (a : Type) => @SAWCoreScaffolding.Nat -> a.

Definition PLiteralSeqBool : forall (n : @Num), @PLiteral (@seq n (@SAWCoreScaffolding.Bool)) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @PLiteral (@seq n1 (@SAWCoreScaffolding.Bool))) (@SAWCoreVectorsAsCoqVectors.bvNat) (@SAWCoreScaffolding.error (@PLiteral (@SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool))) "PLiteralSeqBool: no instance for streams"%string) n.

Definition PLiteralBit : @PLiteral (@SAWCoreScaffolding.Bool) :=
  @SAWCorePrelude.Nat_cases (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.false) (fun (n : @SAWCoreScaffolding.Nat) (b : @SAWCoreScaffolding.Bool) => @SAWCoreScaffolding.true).

Definition PLiteralInteger : @PLiteral (@SAWCoreScaffolding.Integer) :=
  @SAWCoreScaffolding.natToInt.

Definition PLiteralIntMod : forall (n : @SAWCoreScaffolding.Nat), @PLiteral (@SAWCoreScaffolding.IntMod n) :=
  fun (n : @SAWCoreScaffolding.Nat) (x : @SAWCoreScaffolding.Nat) => @SAWCoreScaffolding.toIntMod n (@SAWCoreScaffolding.natToInt x).

Definition PLiteralIntModNum : forall (num : @Num), @PLiteral (@IntModNum num) :=
  fun (num : @Num) => CryptolPrimitives.Num_rect (fun (n : @Num) => @PLiteral (@IntModNum n)) (@PLiteralIntMod) (@PLiteralInteger) num.

Definition PLiteralRational : @PLiteral (@Rational) :=
  fun (x : @SAWCoreScaffolding.Nat) => @SAWCoreScaffolding.error (@Rational) "Unimplemented: Literal Rational"%string.

Definition ecNumber : forall (val : @Num), forall (a : Type), @PLiteral a -> a :=
  fun (val : @Num) (a : Type) (pa : @SAWCoreScaffolding.Nat -> a) => CryptolPrimitives.Num_rect (fun (_1 : @Num) => a) pa (pa 0) val.

Definition ecFromZ : forall (n : @Num), @IntModNum n -> @SAWCoreScaffolding.Integer :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @IntModNum n1 -> @SAWCoreScaffolding.Integer) (@SAWCoreScaffolding.fromIntMod) (fun (x : @SAWCoreScaffolding.Integer) => x) n.

Definition ecFromInteger : forall (a : Type), @PRing a -> @SAWCoreScaffolding.Integer -> a :=
  fun (a : Type) (pa : RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) => RecordProj pa "int".

Definition ecPlus : forall (a : Type), @PRing a -> a -> a -> a :=
  fun (a : Type) (pa : RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) => RecordProj pa "add".

Definition ecMinus : forall (a : Type), @PRing a -> a -> a -> a :=
  fun (a : Type) (pa : RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) => RecordProj pa "sub".

Definition ecMul : forall (a : Type), @PRing a -> a -> a -> a :=
  fun (a : Type) (pa : RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) => RecordProj pa "mul".

Definition ecNeg : forall (a : Type), @PRing a -> a -> a :=
  fun (a : Type) (pa : RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) => RecordProj pa "neg".

Definition ecToInteger : forall (a : Type), @PIntegral a -> a -> @SAWCoreScaffolding.Integer :=
  fun (a : Type) (pa : RecordTypeCons "div" (a -> a -> a) (RecordTypeCons "integralRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "mod" (a -> a -> a) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> a -> r) (RecordTypeCons "toInt" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) => RecordProj pa "toInt".

Definition ecDiv : forall (a : Type), @PIntegral a -> a -> a -> a :=
  fun (a : Type) (pi : RecordTypeCons "div" (a -> a -> a) (RecordTypeCons "integralRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "mod" (a -> a -> a) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> a -> r) (RecordTypeCons "toInt" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) => RecordProj pi "div".

Definition ecMod : forall (a : Type), @PIntegral a -> a -> a -> a :=
  fun (a : Type) (pi : RecordTypeCons "div" (a -> a -> a) (RecordTypeCons "integralRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "mod" (a -> a -> a) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> a -> r) (RecordTypeCons "toInt" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) => RecordProj pi "mod".

Definition ecExp : forall (a : Type), forall (b : Type), @PRing a -> @PIntegral b -> a -> b -> a :=
  fun (a : Type) (b : Type) (pa : RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (pi : RecordTypeCons "div" (b -> b -> b) (RecordTypeCons "integralRing" (RecordTypeCons "add" (b -> b -> b) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> b) (RecordTypeCons "mul" (b -> b -> b) (RecordTypeCons "neg" (b -> b) (RecordTypeCons "ringZero" b (RecordTypeCons "sub" (b -> b -> b) RecordTypeNil)))))) (RecordTypeCons "mod" (b -> b -> b) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> b -> r) (RecordTypeCons "toInt" (b -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (x : a) => RecordProj pi "posNegCases" a (@SAWCorePrelude.expByNat a (RecordProj pa "int" 1%Z) (RecordProj pa "mul") x) (fun (_1 : @SAWCoreScaffolding.Nat) => RecordProj pa "int" 1%Z).

Definition ecRecip : forall (a : Type), @PField a -> a -> a :=
  fun (a : Type) (pf : RecordTypeCons "fieldDiv" (a -> a -> a) (RecordTypeCons "fieldRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "recip" (a -> a) RecordTypeNil))) => RecordProj pf "recip".

Definition ecFieldDiv : forall (a : Type), @PField a -> a -> a -> a :=
  fun (a : Type) (pf : RecordTypeCons "fieldDiv" (a -> a -> a) (RecordTypeCons "fieldRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "recip" (a -> a) RecordTypeNil))) => RecordProj pf "fieldDiv".

Definition ecCeiling : forall (a : Type), @PRound a -> a -> @SAWCoreScaffolding.Integer :=
  fun (a : Type) (pr : RecordTypeCons "ceiling" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "floor" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundAway" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundCmp" (RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (RecordTypeCons "roundField" (RecordTypeCons "fieldDiv" (a -> a -> a) (RecordTypeCons "fieldRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "recip" (a -> a) RecordTypeNil))) (RecordTypeCons "roundToEven" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "trunc" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil))))))) => RecordProj pr "ceiling".

Definition ecFloor : forall (a : Type), @PRound a -> a -> @SAWCoreScaffolding.Integer :=
  fun (a : Type) (pr : RecordTypeCons "ceiling" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "floor" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundAway" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundCmp" (RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (RecordTypeCons "roundField" (RecordTypeCons "fieldDiv" (a -> a -> a) (RecordTypeCons "fieldRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "recip" (a -> a) RecordTypeNil))) (RecordTypeCons "roundToEven" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "trunc" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil))))))) => RecordProj pr "floor".

Definition ecTruncate : forall (a : Type), @PRound a -> a -> @SAWCoreScaffolding.Integer :=
  fun (a : Type) (pr : RecordTypeCons "ceiling" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "floor" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundAway" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundCmp" (RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (RecordTypeCons "roundField" (RecordTypeCons "fieldDiv" (a -> a -> a) (RecordTypeCons "fieldRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "recip" (a -> a) RecordTypeNil))) (RecordTypeCons "roundToEven" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "trunc" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil))))))) => RecordProj pr "trunc".

Definition ecRoundAway : forall (a : Type), @PRound a -> a -> @SAWCoreScaffolding.Integer :=
  fun (a : Type) (pr : RecordTypeCons "ceiling" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "floor" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundAway" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundCmp" (RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (RecordTypeCons "roundField" (RecordTypeCons "fieldDiv" (a -> a -> a) (RecordTypeCons "fieldRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "recip" (a -> a) RecordTypeNil))) (RecordTypeCons "roundToEven" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "trunc" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil))))))) => RecordProj pr "roundAway".

Definition ecRoundToEven : forall (a : Type), @PRound a -> a -> @SAWCoreScaffolding.Integer :=
  fun (a : Type) (pr : RecordTypeCons "ceiling" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "floor" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundAway" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "roundCmp" (RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (RecordTypeCons "roundField" (RecordTypeCons "fieldDiv" (a -> a -> a) (RecordTypeCons "fieldRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "recip" (a -> a) RecordTypeNil))) (RecordTypeCons "roundToEven" (a -> @SAWCoreScaffolding.Integer) (RecordTypeCons "trunc" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil))))))) => RecordProj pr "roundToEven".

Definition ecLg2 : forall (n : @Num), @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @seq n1 (@SAWCoreScaffolding.Bool) -> @seq n1 (@SAWCoreScaffolding.Bool)) (@SAWCoreVectorsAsCoqVectors.bvLg2) (@SAWCoreScaffolding.error (@SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool) -> @SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool)) "ecLg2: expected finite word"%string) n.

Definition ecSDiv : forall (n : @Num), @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @seq n1 (@SAWCoreScaffolding.Bool) -> @seq n1 (@SAWCoreScaffolding.Bool) -> @seq n1 (@SAWCoreScaffolding.Bool)) (@SAWCorePrelude.Nat__rec (fun (n1 : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.Vec n1 (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n1 (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n1 (@SAWCoreScaffolding.Bool)) (@SAWCoreScaffolding.error (@SAWCoreVectorsAsCoqVectors.Vec 0 (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec 0 (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec 0 (@SAWCoreScaffolding.Bool)) "ecSDiv: illegal 0-width word"%string) (fun (n' : @SAWCoreScaffolding.Nat) (_1 : @SAWCoreVectorsAsCoqVectors.Vec n' (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n' (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n' (@SAWCoreScaffolding.Bool)) => @SAWCoreVectorsAsCoqVectors.bvSDiv n')) (@SAWCoreScaffolding.error (@SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool) -> @SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool) -> @SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool)) "ecSDiv: expected finite word"%string) n.

Definition ecSMod : forall (n : @Num), @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @seq n1 (@SAWCoreScaffolding.Bool) -> @seq n1 (@SAWCoreScaffolding.Bool) -> @seq n1 (@SAWCoreScaffolding.Bool)) (@SAWCorePrelude.Nat__rec (fun (n1 : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.Vec n1 (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n1 (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n1 (@SAWCoreScaffolding.Bool)) (@SAWCoreScaffolding.error (@SAWCoreVectorsAsCoqVectors.Vec 0 (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec 0 (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec 0 (@SAWCoreScaffolding.Bool)) "ecSMod: illegal 0-width word"%string) (fun (n' : @SAWCoreScaffolding.Nat) (_1 : @SAWCoreVectorsAsCoqVectors.Vec n' (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n' (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec n' (@SAWCoreScaffolding.Bool)) => @SAWCoreVectorsAsCoqVectors.bvSRem n')) (@SAWCoreScaffolding.error (@SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool) -> @SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool) -> @SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool)) "ecSMod: expected finite word"%string) n.

Definition ecEq : forall (a : Type), @PEq a -> a -> a -> @SAWCoreScaffolding.Bool :=
  fun (a : Type) (pa : RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) => RecordProj pa "eq".

Definition ecNotEq : forall (a : Type), @PEq a -> a -> a -> @SAWCoreScaffolding.Bool :=
  fun (a : Type) (pa : RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) (x : a) (y : a) => @SAWCoreScaffolding.not (@ecEq a pa x y).

Definition ecLt : forall (a : Type), @PCmp a -> a -> a -> @SAWCoreScaffolding.Bool :=
  fun (a : Type) (pa : RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (x : a) (y : a) => RecordProj pa "cmp" x y (@SAWCoreScaffolding.false).

Definition ecGt : forall (a : Type), @PCmp a -> a -> a -> @SAWCoreScaffolding.Bool :=
  fun (a : Type) (pa : RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (x : a) (y : a) => @ecLt a pa y x.

Definition ecLtEq : forall (a : Type), @PCmp a -> a -> a -> @SAWCoreScaffolding.Bool :=
  fun (a : Type) (pa : RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (x : a) (y : a) => @SAWCoreScaffolding.not (@ecLt a pa y x).

Definition ecGtEq : forall (a : Type), @PCmp a -> a -> a -> @SAWCoreScaffolding.Bool :=
  fun (a : Type) (pa : RecordTypeCons "cmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "cmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (x : a) (y : a) => @SAWCoreScaffolding.not (@ecLt a pa x y).

Definition ecSLt : forall (a : Type), @PSignedCmp a -> a -> a -> @SAWCoreScaffolding.Bool :=
  fun (a : Type) (pa : RecordTypeCons "scmp" (a -> a -> @SAWCoreScaffolding.Bool -> @SAWCoreScaffolding.Bool) (RecordTypeCons "signedCmpEq" (RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) RecordTypeNil)) (x : a) (y : a) => RecordProj pa "scmp" x y (@SAWCoreScaffolding.false).

Definition ecAnd : forall (a : Type), @PLogic a -> a -> a -> a :=
  fun (a : Type) (pa : RecordTypeCons "and" (a -> a -> a) (RecordTypeCons "logicZero" a (RecordTypeCons "not" (a -> a) (RecordTypeCons "or" (a -> a -> a) (RecordTypeCons "xor" (a -> a -> a) RecordTypeNil))))) => RecordProj pa "and".

Definition ecOr : forall (a : Type), @PLogic a -> a -> a -> a :=
  fun (a : Type) (pa : RecordTypeCons "and" (a -> a -> a) (RecordTypeCons "logicZero" a (RecordTypeCons "not" (a -> a) (RecordTypeCons "or" (a -> a -> a) (RecordTypeCons "xor" (a -> a -> a) RecordTypeNil))))) => RecordProj pa "or".

Definition ecXor : forall (a : Type), @PLogic a -> a -> a -> a :=
  fun (a : Type) (pa : RecordTypeCons "and" (a -> a -> a) (RecordTypeCons "logicZero" a (RecordTypeCons "not" (a -> a) (RecordTypeCons "or" (a -> a -> a) (RecordTypeCons "xor" (a -> a -> a) RecordTypeNil))))) => RecordProj pa "xor".

Definition ecCompl : forall (a : Type), @PLogic a -> a -> a :=
  fun (a : Type) (pa : RecordTypeCons "and" (a -> a -> a) (RecordTypeCons "logicZero" a (RecordTypeCons "not" (a -> a) (RecordTypeCons "or" (a -> a -> a) (RecordTypeCons "xor" (a -> a -> a) RecordTypeNil))))) => RecordProj pa "not".

Definition ecZero : forall (a : Type), @PZero a -> a :=
  fun (a : Type) (pa : a) => pa.

Definition ecFraction : forall (a : Type), a :=
  fun (a : Type) => @SAWCoreScaffolding.error a "Unimplemented: fraction"%string.

Definition ecShiftL : forall (m : @Num), forall (ix : Type), forall (a : Type), @PIntegral ix -> @PZero a -> @seq m a -> ix -> @seq m a :=
  fun (m : @Num) => CryptolPrimitives.Num_rect (fun (m1 : @Num) => forall (ix : Type), forall (a : Type), @PIntegral ix -> @PZero a -> @seq m1 a -> ix -> @seq m1 a) (fun (m1 : @SAWCoreScaffolding.Nat) (ix : Type) (a : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (pz : a) (xs : @SAWCoreVectorsAsCoqVectors.Vec m1 a) => RecordProj pix "posNegCases" (@SAWCoreVectorsAsCoqVectors.Vec m1 a) (@SAWCoreVectorsAsCoqVectors.shiftL m1 a (@ecZero a pz) xs) (@SAWCoreVectorsAsCoqVectors.shiftR m1 a (@ecZero a pz) xs)) (fun (ix : Type) (a : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (pz : a) (xs : @SAWCorePrelude.Stream a) => RecordProj pix "posNegCases" (@SAWCorePrelude.Stream a) (@SAWCorePrelude.streamShiftL a xs) (@SAWCorePrelude.streamShiftR a pz xs)) m.

Definition ecShiftR : forall (m : @Num), forall (ix : Type), forall (a : Type), @PIntegral ix -> @PZero a -> @seq m a -> ix -> @seq m a :=
  fun (m : @Num) => CryptolPrimitives.Num_rect (fun (m1 : @Num) => forall (ix : Type), forall (a : Type), @PIntegral ix -> @PZero a -> @seq m1 a -> ix -> @seq m1 a) (fun (m1 : @SAWCoreScaffolding.Nat) (ix : Type) (a : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (pz : a) (xs : @SAWCoreVectorsAsCoqVectors.Vec m1 a) => RecordProj pix "posNegCases" (@SAWCoreVectorsAsCoqVectors.Vec m1 a) (@SAWCoreVectorsAsCoqVectors.shiftR m1 a (@ecZero a pz) xs) (@SAWCoreVectorsAsCoqVectors.shiftL m1 a (@ecZero a pz) xs)) (fun (ix : Type) (a : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (pz : a) (xs : @SAWCorePrelude.Stream a) => RecordProj pix "posNegCases" (@SAWCorePrelude.Stream a) (@SAWCorePrelude.streamShiftR a pz xs) (@SAWCorePrelude.streamShiftL a xs)) m.

Definition ecSShiftR : forall (n : @Num), forall (ix : Type), @PIntegral ix -> @seq n (@SAWCoreScaffolding.Bool) -> ix -> @seq n (@SAWCoreScaffolding.Bool) :=
  @finNumRec (fun (n : @Num) => forall (ix : Type), @PIntegral ix -> @seq n (@SAWCoreScaffolding.Bool) -> ix -> @seq n (@SAWCoreScaffolding.Bool)) (fun (n : @SAWCoreScaffolding.Nat) (ix : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) => @SAWCorePrelude.natCase (fun (w : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.Vec w (@SAWCoreScaffolding.Bool) -> ix -> @SAWCoreVectorsAsCoqVectors.Vec w (@SAWCoreScaffolding.Bool)) (fun (xs : @SAWCoreVectorsAsCoqVectors.Vec 0 (@SAWCoreScaffolding.Bool)) (_1 : ix) => xs) (fun (w : @SAWCoreScaffolding.Nat) (xs : @SAWCoreVectorsAsCoqVectors.Vec (@SAWCoreScaffolding.Succ w) (@SAWCoreScaffolding.Bool)) => RecordProj pix "posNegCases" (@SAWCoreVectorsAsCoqVectors.Vec (@SAWCoreScaffolding.Succ w) (@SAWCoreScaffolding.Bool)) (@SAWCoreVectorsAsCoqVectors.bvSShr w xs) (@SAWCorePrelude.bvShl (@SAWCoreScaffolding.Succ w) xs)) n).

Definition ecRotL : forall (m : @Num), forall (ix : Type), forall (a : Type), @PIntegral ix -> @seq m a -> ix -> @seq m a :=
  @finNumRec (fun (m : @Num) => forall (ix : Type), forall (a : Type), @PIntegral ix -> @seq m a -> ix -> @seq m a) (fun (m : @SAWCoreScaffolding.Nat) (ix : Type) (a : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (xs : @SAWCoreVectorsAsCoqVectors.Vec m a) => RecordProj pix "posNegCases" (@SAWCoreVectorsAsCoqVectors.Vec m a) (@SAWCoreVectorsAsCoqVectors.rotateL m a xs) (@SAWCoreVectorsAsCoqVectors.rotateR m a xs)).

Definition ecRotR : forall (m : @Num), forall (ix : Type), forall (a : Type), @PIntegral ix -> @seq m a -> ix -> @seq m a :=
  @finNumRec (fun (m : @Num) => forall (ix : Type), forall (a : Type), @PIntegral ix -> @seq m a -> ix -> @seq m a) (fun (m : @SAWCoreScaffolding.Nat) (ix : Type) (a : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (xs : @SAWCoreVectorsAsCoqVectors.Vec m a) => RecordProj pix "posNegCases" (@SAWCoreVectorsAsCoqVectors.Vec m a) (@SAWCoreVectorsAsCoqVectors.rotateR m a xs) (@SAWCoreVectorsAsCoqVectors.rotateL m a xs)).

Definition ecCat : forall (m : @Num), forall (n : @Num), forall (a : Type), @seq m a -> @seq n a -> @seq (@tcAdd m n) a :=
  @finNumRec (fun (m : @Num) => forall (n : @Num), forall (a : Type), @seq m a -> @seq n a -> @seq (@tcAdd m n) a) (fun (m : @SAWCoreScaffolding.Nat) => @CryptolPrimitives.Num_rect (fun (n : @Num) => forall (a : Type), @SAWCoreVectorsAsCoqVectors.Vec m a -> @seq n a -> @seq (@tcAdd (@TCNum m) n) a) (fun (n : @SAWCoreScaffolding.Nat) (a : Type) => @SAWCorePrelude.append m n a) (fun (a : Type) => @SAWCorePrelude.streamAppend a m)).

Definition ecSplitAt : forall (m : @Num), forall (n : @Num), forall (a : Type), @seq (@tcAdd m n) a -> prod (@seq m a) (@seq n a) :=
  @finNumRec (fun (m : @Num) => forall (n : @Num), forall (a : Type), @seq (@tcAdd m n) a -> prod (@seq m a) (@seq n a)) (fun (m : @SAWCoreScaffolding.Nat) => @CryptolPrimitives.Num_rect (fun (n : @Num) => forall (a : Type), @seq (@tcAdd (@TCNum m) n) a -> prod (@SAWCoreVectorsAsCoqVectors.Vec m a) (@seq n a)) (fun (n : @SAWCoreScaffolding.Nat) (a : Type) (xs : @SAWCoreVectorsAsCoqVectors.Vec (@SAWCorePrelude.addNat m n) a) => pair (@SAWCorePrelude.take a m n xs) (@SAWCorePrelude.drop a m n xs)) (fun (a : Type) (xs : @SAWCorePrelude.Stream a) => pair (@SAWCorePrelude.streamTake a m xs) (@SAWCorePrelude.streamDrop a m xs))).

Definition ecJoin : forall (m : @Num), forall (n : @Num), forall (a : Type), @seq m (@seq n a) -> @seq (@tcMul m n) a :=
  fun (m : @Num) => CryptolPrimitives.Num_rect (fun (m1 : @Num) => forall (n : @Num), forall (a : Type), @seq m1 (@seq n a) -> @seq (@tcMul m1 n) a) (fun (m1 : @SAWCoreScaffolding.Nat) => @finNumRec (fun (n : @Num) => forall (a : Type), @SAWCoreVectorsAsCoqVectors.Vec m1 (@seq n a) -> @seq (@tcMul (@TCNum m1) n) a) (fun (n : @SAWCoreScaffolding.Nat) (a : Type) => @SAWCorePrelude.join m1 n a)) (@finNumRec (fun (n : @Num) => forall (a : Type), @SAWCorePrelude.Stream (@seq n a) -> @seq (@tcMul (@TCInf) n) a) (fun (n : @SAWCoreScaffolding.Nat) (a : Type) => @SAWCorePrelude.natCase (fun (n' : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.Stream (@SAWCoreVectorsAsCoqVectors.Vec n' a) -> @seq (@SAWCorePrelude.if0Nat (@Num) n' (@TCNum 0) (@TCInf)) a) (fun (s : @SAWCorePrelude.Stream (@SAWCoreVectorsAsCoqVectors.Vec 0 a)) => @SAWCoreVectorsAsCoqVectors.EmptyVec a) (fun (n' : @SAWCoreScaffolding.Nat) (s : @SAWCorePrelude.Stream (@SAWCoreVectorsAsCoqVectors.Vec (@SAWCoreScaffolding.Succ n') a)) => @SAWCorePrelude.streamJoin a n' s) n)) m.

Definition ecSplit : forall (m : @Num), forall (n : @Num), forall (a : Type), @seq (@tcMul m n) a -> @seq m (@seq n a) :=
  fun (m : @Num) => CryptolPrimitives.Num_rect (fun (m1 : @Num) => forall (n : @Num), forall (a : Type), @seq (@tcMul m1 n) a -> @seq m1 (@seq n a)) (fun (m1 : @SAWCoreScaffolding.Nat) => @finNumRec (fun (n : @Num) => forall (a : Type), @seq (@tcMul (@TCNum m1) n) a -> @SAWCoreVectorsAsCoqVectors.Vec m1 (@seq n a)) (fun (n : @SAWCoreScaffolding.Nat) (a : Type) => @SAWCorePrelude.split m1 n a)) (@finNumRec (fun (n : @Num) => forall (a : Type), @seq (@tcMul (@TCInf) n) a -> @SAWCorePrelude.Stream (@seq n a)) (fun (n : @SAWCoreScaffolding.Nat) (a : Type) => @SAWCorePrelude.natCase (fun (n' : @SAWCoreScaffolding.Nat) => @seq (@SAWCorePrelude.if0Nat (@Num) n' (@TCNum 0) (@TCInf)) a -> @SAWCorePrelude.Stream (@SAWCoreVectorsAsCoqVectors.Vec n' a)) (@SAWCorePrelude.streamConst (@SAWCoreVectorsAsCoqVectors.Vec 0 a)) (fun (n' : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.streamSplit a (@SAWCoreScaffolding.Succ n')) n)) m.

Definition ecReverse : forall (n : @Num), forall (a : Type), @seq n a -> @seq n a :=
  @finNumRec (fun (n : @Num) => forall (a : Type), @seq n a -> @seq n a) (@SAWCorePrelude.reverse).

Definition ecTranspose : forall (m : @Num), forall (n : @Num), forall (a : Type), @seq m (@seq n a) -> @seq n (@seq m a) :=
  fun (m : @Num) (n : @Num) (a : Type) => CryptolPrimitives.Num_rect (fun (m1 : @Num) => @seq m1 (@seq n a) -> @seq n (@seq m1 a)) (fun (m1 : @SAWCoreScaffolding.Nat) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @SAWCoreVectorsAsCoqVectors.Vec m1 (@seq n1 a) -> @seq n1 (@SAWCoreVectorsAsCoqVectors.Vec m1 a)) (fun (n1 : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.transpose m1 n1 a) (fun (xss : @SAWCoreVectorsAsCoqVectors.Vec m1 (@SAWCorePrelude.Stream a)) => @SAWCorePrelude.MkStream (@SAWCoreVectorsAsCoqVectors.Vec m1 a) (fun (i : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.gen m1 a (fun (j : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.streamGet a (@SAWCorePrelude.sawAt m1 (@SAWCorePrelude.Stream a) xss j) i))) n) (CryptolPrimitives.Num_rect (fun (n1 : @Num) => @SAWCorePrelude.Stream (@seq n1 a) -> @seq n1 (@SAWCorePrelude.Stream a)) (fun (n1 : @SAWCoreScaffolding.Nat) (xss : @SAWCorePrelude.Stream (@SAWCoreVectorsAsCoqVectors.Vec n1 a)) => @SAWCoreVectorsAsCoqVectors.gen n1 (@SAWCorePrelude.Stream a) (fun (i : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.MkStream a (fun (j : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.sawAt n1 a (@SAWCorePrelude.streamGet (@SAWCoreVectorsAsCoqVectors.Vec n1 a) xss j) i))) (fun (xss : @SAWCorePrelude.Stream (@SAWCorePrelude.Stream a)) => @SAWCorePrelude.MkStream (@SAWCorePrelude.Stream a) (fun (i : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.MkStream a (fun (j : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.streamGet a (@SAWCorePrelude.streamGet (@SAWCorePrelude.Stream a) xss j) i))) n) m.

Definition ecAt : forall (n : @Num), forall (a : Type), forall (ix : Type), @PIntegral ix -> @seq n a -> ix -> a :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => forall (a : Type), forall (ix : Type), @PIntegral ix -> @seq n1 a -> ix -> a) (fun (n1 : @SAWCoreScaffolding.Nat) (a : Type) (ix : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (xs : @SAWCoreVectorsAsCoqVectors.Vec n1 a) => RecordProj pix "posNegCases" a (@SAWCorePrelude.sawAt n1 a xs) (fun (_1 : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.sawAt n1 a xs 0)) (fun (a : Type) (ix : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (xs : @SAWCorePrelude.Stream a) => RecordProj pix "posNegCases" a (@SAWCorePrelude.streamGet a xs) (fun (_1 : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.streamGet a xs 0)) n.

Definition ecAtBack : forall (n : @Num), forall (a : Type), forall (ix : Type), @PIntegral ix -> @seq n a -> ix -> a :=
  fun (n : @Num) (a : Type) (ix : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (xs : CryptolPrimitives.Num_rect (fun (num : @Num) => Type) (fun (n1 : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.Vec n1 a) (@SAWCorePrelude.Stream a) n) => @ecAt n a ix pix (@ecReverse n a xs).

Definition ecFromTo : forall (first : @Num), forall (last : @Num), forall (a : Type), @PLiteral a -> @PLiteral a -> @seq (@tcAdd (@TCNum 1) (@tcSub last first)) a :=
  @finNumRec (fun (first : @Num) => forall (last : @Num), forall (a : Type), @PLiteral a -> @PLiteral a -> @seq (@tcAdd (@TCNum 1) (@tcSub last first)) a) (fun (first : @SAWCoreScaffolding.Nat) => @finNumRec (fun (last : @Num) => forall (a : Type), @PLiteral a -> @PLiteral a -> @seq (@tcAdd (@TCNum 1) (@tcSub last (@TCNum first))) a) (fun (last : @SAWCoreScaffolding.Nat) (a : Type) (pa : @SAWCoreScaffolding.Nat -> a) (_1 : @SAWCoreScaffolding.Nat -> a) => @SAWCoreVectorsAsCoqVectors.gen (@SAWCorePrelude.addNat 1 (@SAWCorePrelude.subNat last first)) a (fun (i : @SAWCoreScaffolding.Nat) => pa (@SAWCorePrelude.addNat i first)))).

Definition ecFromThenTo : forall (first : @Num), forall (next : @Num), forall (last : @Num), forall (a : Type), forall (len : @Num), @PLiteral a -> @PLiteral a -> @PLiteral a -> @seq len a :=
  fun (first : @Num) (next : @Num) (_1 : @Num) (a : Type) => @finNumRec (fun (len : @Num) => @PLiteral a -> @PLiteral a -> @PLiteral a -> @seq len a) (fun (len : @SAWCoreScaffolding.Nat) (pa : @SAWCoreScaffolding.Nat -> a) (_2 : @SAWCoreScaffolding.Nat -> a) (_3 : @SAWCoreScaffolding.Nat -> a) => @SAWCoreVectorsAsCoqVectors.gen len a (fun (i : @SAWCoreScaffolding.Nat) => pa (@SAWCorePrelude.subNat (@SAWCorePrelude.addNat (@getFinNat first) (@SAWCorePrelude.mulNat i (@getFinNat next))) (@SAWCorePrelude.mulNat i (@getFinNat first))))).

Definition ecInfFrom : forall (a : Type), @PIntegral a -> a -> @seq (@TCInf) a :=
  fun (a : Type) (pa : RecordTypeCons "div" (a -> a -> a) (RecordTypeCons "integralRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "mod" (a -> a -> a) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> a -> r) (RecordTypeCons "toInt" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (x : a) => @SAWCorePrelude.MkStream a (fun (i : @SAWCoreScaffolding.Nat) => RecordProj (RecordProj pa "integralRing") "add" x (RecordProj (RecordProj pa "integralRing") "int" (@SAWCoreScaffolding.natToInt i))).

Definition ecInfFromThen : forall (a : Type), @PIntegral a -> a -> a -> @seq (@TCInf) a :=
  fun (a : Type) (pa : RecordTypeCons "div" (a -> a -> a) (RecordTypeCons "integralRing" (RecordTypeCons "add" (a -> a -> a) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> a) (RecordTypeCons "mul" (a -> a -> a) (RecordTypeCons "neg" (a -> a) (RecordTypeCons "ringZero" a (RecordTypeCons "sub" (a -> a -> a) RecordTypeNil)))))) (RecordTypeCons "mod" (a -> a -> a) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> a -> r) (RecordTypeCons "toInt" (a -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (x : a) (y : a) => @SAWCorePrelude.MkStream a (fun (i : @SAWCoreScaffolding.Nat) => RecordProj (RecordProj pa "integralRing") "add" x (RecordProj (RecordProj pa "integralRing") "mul" (RecordProj (RecordProj pa "integralRing") "sub" y x) (RecordProj (RecordProj pa "integralRing") "int" (@SAWCoreScaffolding.natToInt i)))).

Definition ecError : forall (a : Type), forall (len : @Num), @seq len (@SAWCoreVectorsAsCoqVectors.Vec 8 (@SAWCoreScaffolding.Bool)) -> a :=
  fun (a : Type) (len : @Num) (msg : CryptolPrimitives.Num_rect (fun (num : @Num) => Type) (fun (n : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreVectorsAsCoqVectors.Vec 8 (@SAWCoreScaffolding.Bool))) (@SAWCorePrelude.Stream (@SAWCoreVectorsAsCoqVectors.Vec 8 (@SAWCoreScaffolding.Bool))) len) => @SAWCoreScaffolding.error a "encountered call to the Cryptol 'error' function"%string.

Definition ecRandom : forall (a : Type), @SAWCoreVectorsAsCoqVectors.Vec 32 (@SAWCoreScaffolding.Bool) -> a :=
  fun (a : Type) (_1 : @SAWCoreVectorsAsCoqVectors.Vec 32 (@SAWCoreScaffolding.Bool)) => @SAWCoreScaffolding.error a "Cryptol.random"%string.

Definition ecTrace : forall (n : @Num), forall (a : Type), forall (b : Type), @seq n (@SAWCoreVectorsAsCoqVectors.Vec 8 (@SAWCoreScaffolding.Bool)) -> a -> b -> b :=
  fun (_1 : @Num) (_2 : Type) (_3 : Type) (_4 : CryptolPrimitives.Num_rect (fun (num : @Num) => Type) (fun (n : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreVectorsAsCoqVectors.Vec 8 (@SAWCoreScaffolding.Bool))) (@SAWCorePrelude.Stream (@SAWCoreVectorsAsCoqVectors.Vec 8 (@SAWCoreScaffolding.Bool))) _1) (_5 : _2) (x : _3) => x.

Definition ecDeepseq : forall (a : Type), forall (b : Type), @PEq a -> a -> b -> b :=
  fun (a : Type) (b : Type) (pa : RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) (x : a) (y : b) => y.

Definition ecParmap : forall (a : Type), forall (b : Type), forall (n : @Num), @PEq b -> (a -> b) -> @seq n a -> @seq n b :=
  fun (a : Type) (b : Type) (n : @Num) (pb : RecordTypeCons "eq" (b -> b -> @SAWCoreScaffolding.Bool) RecordTypeNil) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => (a -> b) -> @seq n1 a -> @seq n1 b) (fun (n1 : @SAWCoreScaffolding.Nat) (f : a -> b) (xs : @SAWCoreVectorsAsCoqVectors.Vec n1 a) => @SAWCorePrelude.map a b f n1 xs) (fun (f : a -> b) (xs : @SAWCorePrelude.Stream a) => @SAWCoreScaffolding.error (@SAWCorePrelude.Stream b) "Unexpected infinite stream in parmap"%string) n.

Definition ecFoldl : forall (n : @Num), forall (a : Type), forall (b : Type), (a -> b -> a) -> a -> @seq n b -> a :=
  fun (n : @Num) (a : Type) (b : Type) (f : a -> b -> a) (z : a) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => @seq n1 b -> a) (fun (n1 : @SAWCoreScaffolding.Nat) (xs : @SAWCoreVectorsAsCoqVectors.Vec n1 b) => @SAWCoreVectorsAsCoqVectors.foldr b a n1 (fun (y : b) (x : a) => f x y) z (@SAWCorePrelude.reverse n1 b xs)) (fun (xs : @SAWCorePrelude.Stream b) => @SAWCoreScaffolding.error a "Unexpected infinite stream in foldl"%string) n.

Definition ecFoldlPrime : forall (n : @Num), forall (a : Type), forall (b : Type), @PEq a -> (a -> b -> a) -> a -> @seq n b -> a :=
  fun (n : @Num) (a : Type) (b : Type) (pa : RecordTypeCons "eq" (a -> a -> @SAWCoreScaffolding.Bool) RecordTypeNil) => @ecFoldl n a b.

Definition TCFloat : @Num -> @Num -> Type :=
  fun (_1 : @Num) (_2 : @Num) => unit.

Definition PEqFloat : forall (e : @Num), forall (p : @Num), @PEq (@TCFloat e p) :=
  fun (e : @Num) (p : @Num) => RecordCons "eq" (fun (x : unit) (y : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Bool) "Unimplemented: (==) Float"%string) RecordNil.

Definition PCmpFloat : forall (e : @Num), forall (p : @Num), @PCmp (@TCFloat e p) :=
  fun (e : @Num) (p : @Num) => RecordCons "cmp" (fun (x : unit) (y : unit) (k : @SAWCoreScaffolding.Bool) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Bool) "Unimplemented: Cmp Float"%string) (RecordCons "cmpEq" (@PEqFloat e p) RecordNil).

Definition PZeroFloat : forall (e : @Num), forall (p : @Num), @PZero (@TCFloat e p) :=
  fun (e : @Num) (p : @Num) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: Zero Float"%string.

Definition PRingFloat : forall (e : @Num), forall (p : @Num), @PRing (@TCFloat e p) :=
  fun (e : @Num) (p : @Num) => RecordCons "add" (fun (x : unit) (y : unit) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: (+) Float"%string) (RecordCons "int" (fun (i : @SAWCoreScaffolding.Integer) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: toInteger Float"%string) (RecordCons "mul" (fun (x : unit) (y : unit) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: (*) Float"%string) (RecordCons "neg" (fun (x : unit) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: neg Float"%string) (RecordCons "ringZero" (@PZeroFloat e p) (RecordCons "sub" (fun (x : unit) (y : unit) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: (-) Float"%string) RecordNil))))).

Definition PFieldFloat : forall (e : @Num), forall (p : @Num), @PField (@TCFloat e p) :=
  fun (e : @Num) (p : @Num) => RecordCons "fieldDiv" (fun (x : unit) (y : unit) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: (/.) Float"%string) (RecordCons "fieldRing" (@PRingFloat e p) (RecordCons "recip" (fun (x : unit) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: recip Float"%string) RecordNil)).

Definition PRoundFloat : forall (e : @Num), forall (p : @Num), @PRound (@TCFloat e p) :=
  fun (e : @Num) (p : @Num) => RecordCons "ceiling" (fun (x : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Integer) "Unimplemented: ceiling Float"%string) (RecordCons "floor" (fun (x : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Integer) "Unimplemented: floor Float"%string) (RecordCons "roundAway" (fun (x : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Integer) "Unimplemented: roundAway Float"%string) (RecordCons "roundCmp" (@PCmpFloat e p) (RecordCons "roundField" (@PFieldFloat e p) (RecordCons "roundToEven" (fun (x : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Integer) "Unimplemented: roundToEven Float"%string) (RecordCons "trunc" (fun (x : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Integer) "Unimplemented: trunc Float"%string) RecordNil)))))).

Definition ecFpNaN : forall (e : @Num), forall (p : @Num), @TCFloat e p :=
  fun (e : @Num) (p : @Num) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: fpNaN"%string.

Definition ecFpPosInf : forall (e : @Num), forall (p : @Num), @TCFloat e p :=
  fun (e : @Num) (p : @Num) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: fpPosInf"%string.

Definition ecFpFromBits : forall (e : @Num), forall (p : @Num), @seq (@tcAdd e p) (@SAWCoreScaffolding.Bool) -> @TCFloat e p :=
  fun (e : @Num) (p : @Num) (_1 : CryptolPrimitives.Num_rect (fun (num : @Num) => Type) (fun (n : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) (@SAWCorePrelude.Stream (@SAWCoreScaffolding.Bool)) (CryptolPrimitives.Num_rect (fun (num1' : @Num) => @Num) (fun (n1 : @SAWCoreScaffolding.Nat) => CryptolPrimitives.Num_rect (fun (num2' : @Num) => @Num) (fun (n2 : @SAWCoreScaffolding.Nat) => @TCNum (@SAWCorePrelude.addNat n1 n2)) ((fun (x : @SAWCoreScaffolding.Nat) => @TCInf) n1) p) (CryptolPrimitives.Num_rect (fun (num2' : @Num) => @Num) (fun (y : @SAWCoreScaffolding.Nat) => @TCInf) (@TCInf) p) e)) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: fpFromBits"%string.

Definition ecFpToBits : forall (e : @Num), forall (p : @Num), @TCFloat e p -> @seq (@tcAdd e p) (@SAWCoreScaffolding.Bool) :=
  fun (e : @Num) (p : @Num) (_1 : unit) => @SAWCoreScaffolding.error (@seq (@tcAdd e p) (@SAWCoreScaffolding.Bool)) "Unimplemented: fpToBits"%string.

Definition ecFpEq : forall (e : @Num), forall (p : @Num), @TCFloat e p -> @TCFloat e p -> @SAWCoreScaffolding.Bool :=
  fun (e : @Num) (p : @Num) (_1 : unit) (_2 : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Bool) "Unimplemented: =.="%string.

Definition ecFpAdd : forall (e : @Num), forall (p : @Num), @SAWCoreVectorsAsCoqVectors.Vec 3 (@SAWCoreScaffolding.Bool) -> @TCFloat e p -> @TCFloat e p -> @TCFloat e p :=
  fun (e : @Num) (p : @Num) (_1 : @SAWCoreVectorsAsCoqVectors.Vec 3 (@SAWCoreScaffolding.Bool)) (_2 : unit) (_3 : unit) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: fpAdd"%string.

Definition ecFpSub : forall (e : @Num), forall (p : @Num), @SAWCoreVectorsAsCoqVectors.Vec 3 (@SAWCoreScaffolding.Bool) -> @TCFloat e p -> @TCFloat e p -> @TCFloat e p :=
  fun (e : @Num) (p : @Num) (_1 : @SAWCoreVectorsAsCoqVectors.Vec 3 (@SAWCoreScaffolding.Bool)) (_2 : unit) (_3 : unit) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: fpSub"%string.

Definition ecFpMul : forall (e : @Num), forall (p : @Num), @SAWCoreVectorsAsCoqVectors.Vec 3 (@SAWCoreScaffolding.Bool) -> @TCFloat e p -> @TCFloat e p -> @TCFloat e p :=
  fun (e : @Num) (p : @Num) (_1 : @SAWCoreVectorsAsCoqVectors.Vec 3 (@SAWCoreScaffolding.Bool)) (_2 : unit) (_3 : unit) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: fpMul"%string.

Definition ecFpDiv : forall (e : @Num), forall (p : @Num), @SAWCoreVectorsAsCoqVectors.Vec 3 (@SAWCoreScaffolding.Bool) -> @TCFloat e p -> @TCFloat e p -> @TCFloat e p :=
  fun (e : @Num) (p : @Num) (_1 : @SAWCoreVectorsAsCoqVectors.Vec 3 (@SAWCoreScaffolding.Bool)) (_2 : unit) (_3 : unit) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: fpDiv"%string.

Definition ecFpIsFinite : forall (e : @Num), forall (p : @Num), @TCFloat e p -> @SAWCoreScaffolding.Bool :=
  fun (e : @Num) (p : @Num) (_1 : unit) => @SAWCoreScaffolding.error (@SAWCoreScaffolding.Bool) "Unimplemented: fpIsFinite"%string.

Definition ecFpToRational : forall (e : @Num), forall (p : @Num), @TCFloat e p -> @Rational :=
  fun (e : @Num) (p : @Num) (_1 : unit) => @SAWCoreScaffolding.error (@Rational) "Unimplemented: fpToRational"%string.

Definition ecFpFromRational : forall (e : @Num), forall (p : @Num), @SAWCoreVectorsAsCoqVectors.Vec 3 (@SAWCoreScaffolding.Bool) -> @Rational -> @TCFloat e p :=
  fun (e : @Num) (p : @Num) (_1 : @SAWCoreVectorsAsCoqVectors.Vec 3 (@SAWCoreScaffolding.Bool)) (_2 : unit) => @SAWCoreScaffolding.error (@TCFloat e p) "Unimplemented: fpFromRational"%string.

Definition ecUpdate : forall (n : @Num), forall (a : Type), forall (ix : Type), @PIntegral ix -> @seq n a -> ix -> a -> @seq n a :=
  fun (n : @Num) => CryptolPrimitives.Num_rect (fun (n1 : @Num) => forall (a : Type), forall (ix : Type), @PIntegral ix -> @seq n1 a -> ix -> a -> @seq n1 a) (fun (n1 : @SAWCoreScaffolding.Nat) (a : Type) (ix : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (xs : @SAWCoreVectorsAsCoqVectors.Vec n1 a) => RecordProj pix "posNegCases" (a -> @SAWCoreVectorsAsCoqVectors.Vec n1 a) (@SAWCorePrelude.upd n1 a xs) (fun (_1 : @SAWCoreScaffolding.Nat) (_2 : a) => xs)) (fun (a : Type) (ix : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (xs : @SAWCorePrelude.Stream a) => RecordProj pix "posNegCases" (a -> @SAWCorePrelude.Stream a) (@SAWCorePrelude.streamUpd a xs) (fun (_1 : @SAWCoreScaffolding.Nat) (_2 : a) => xs)) n.

Definition ecUpdateEnd : forall (n : @Num), forall (a : Type), forall (ix : Type), @PIntegral ix -> @seq n a -> ix -> a -> @seq n a :=
  @finNumRec (fun (n : @Num) => forall (a : Type), forall (ix : Type), @PIntegral ix -> @seq n a -> ix -> a -> @seq n a) (fun (n : @SAWCoreScaffolding.Nat) (a : Type) (ix : Type) (pix : RecordTypeCons "div" (ix -> ix -> ix) (RecordTypeCons "integralRing" (RecordTypeCons "add" (ix -> ix -> ix) (RecordTypeCons "int" (@SAWCoreScaffolding.Integer -> ix) (RecordTypeCons "mul" (ix -> ix -> ix) (RecordTypeCons "neg" (ix -> ix) (RecordTypeCons "ringZero" ix (RecordTypeCons "sub" (ix -> ix -> ix) RecordTypeNil)))))) (RecordTypeCons "mod" (ix -> ix -> ix) (RecordTypeCons "posNegCases" (forall (r : Type), (@SAWCoreScaffolding.Nat -> r) -> (@SAWCoreScaffolding.Nat -> r) -> ix -> r) (RecordTypeCons "toInt" (ix -> @SAWCoreScaffolding.Integer) RecordTypeNil))))) (xs : @SAWCoreVectorsAsCoqVectors.Vec n a) => RecordProj pix "posNegCases" (a -> @SAWCoreVectorsAsCoqVectors.Vec n a) (fun (i : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.upd n a xs (@SAWCorePrelude.subNat (@SAWCorePrelude.subNat n 1) i)) (fun (_1 : @SAWCoreScaffolding.Nat) (_2 : a) => xs)).

Definition ecTrunc : forall (m : @Num), forall (n : @Num), @seq (@tcAdd m n) (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) :=
  @finNumRec2 (fun (m : @Num) (n : @Num) => @seq (@tcAdd m n) (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool)) (@SAWCorePrelude.bvTrunc).

Definition ecUExt : forall (m : @Num), forall (n : @Num), @seq n (@SAWCoreScaffolding.Bool) -> @seq (@tcAdd m n) (@SAWCoreScaffolding.Bool) :=
  @finNumRec2 (fun (m : @Num) (n : @Num) => @seq n (@SAWCoreScaffolding.Bool) -> @seq (@tcAdd m n) (@SAWCoreScaffolding.Bool)) (@SAWCorePrelude.bvUExt).

Definition ecSExt : forall (m : @Num), forall (n : @Num), @seq n (@SAWCoreScaffolding.Bool) -> @seq (@tcAdd m n) (@SAWCoreScaffolding.Bool) :=
  @finNumRec2 (fun (m : @Num) (n : @Num) => @seq n (@SAWCoreScaffolding.Bool) -> @seq (@tcAdd m n) (@SAWCoreScaffolding.Bool)) (fun (m : @SAWCoreScaffolding.Nat) (n : @SAWCoreScaffolding.Nat) => @SAWCorePrelude.natCase (fun (n' : @SAWCoreScaffolding.Nat) => @SAWCoreVectorsAsCoqVectors.Vec n' (@SAWCoreScaffolding.Bool) -> @SAWCoreVectorsAsCoqVectors.Vec (@SAWCorePrelude.addNat m n') (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 0 (@SAWCoreScaffolding.Bool)) => @SAWCoreVectorsAsCoqVectors.bvNat (@SAWCorePrelude.addNat m 0) 0) (@SAWCorePrelude.bvSExt m) n).

Definition ecSgt : forall (n : @Num), @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool :=
  @finNumRec (fun (n : @Num) => @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvsgt).

Definition ecSge : forall (n : @Num), @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool :=
  @finNumRec (fun (n : @Num) => @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvsge).

Definition ecSlt : forall (n : @Num), @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool :=
  @finNumRec (fun (n : @Num) => @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvslt).

Definition ecSle : forall (n : @Num), @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool :=
  @finNumRec (fun (n : @Num) => @seq n (@SAWCoreScaffolding.Bool) -> @seq n (@SAWCoreScaffolding.Bool) -> @SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvsle).

Definition ecArrayConstant : forall (a : Type), forall (b : Type), b -> @SAWCorePrelude.Array a b :=
  @SAWCorePrelude.arrayConstant.

Definition ecArrayLookup : forall (a : Type), forall (b : Type), @SAWCorePrelude.Array a b -> a -> b :=
  @SAWCorePrelude.arrayLookup.

Definition ecArrayUpdate : forall (a : Type), forall (b : Type), @SAWCorePrelude.Array a b -> a -> b -> @SAWCorePrelude.Array a b :=
  @SAWCorePrelude.arrayUpdate.

Axiom replicate_False : forall (n : @SAWCoreScaffolding.Nat), @SAWCoreScaffolding.Eq (@SAWCoreVectorsAsCoqVectors.Vec n (@SAWCoreScaffolding.Bool)) (@SAWCorePrelude.replicate n (@SAWCoreScaffolding.Bool) (@SAWCoreScaffolding.false)) (@SAWCoreVectorsAsCoqVectors.bvNat n 0) .

Axiom subNat_0 : forall (n : @SAWCoreScaffolding.Nat), @SAWCoreScaffolding.Eq (@SAWCoreScaffolding.Nat) (@SAWCorePrelude.subNat n 0) n .

End CryptolPrimitives.
