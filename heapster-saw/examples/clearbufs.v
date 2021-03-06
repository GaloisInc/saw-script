
(** Mandatory imports from saw-core-coq *)
From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
Import ListNotations.

(** Post-preamble section specified by you *)
From CryptolToCoq Require Import SAWCorePrelude.

(** Code generated by saw-core-coq *)

Module clearbufs.

Definition BV64 : Type :=
  @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (_1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit).

Definition V64 : Type :=
  @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool).

Definition bv64_16 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool) :=
  intToBv 64 0x10%Z.

Inductive Mbox : Type :=
| Mbox_nil : @Mbox
| Mbox_cons : @Mbox -> forall (len : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)), @SAWCorePrelude.BVVec 64 len BV64 -> @Mbox
.

Definition Mbox_def : Type :=
  @Mbox.

Axiom unfoldMbox : @Mbox -> @SAWCorePrelude.Either unit (@sigT V64 (fun (len : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod (@Mbox) (prod (@SAWCorePrelude.BVVec 64 len BV64) unit))) .

Axiom foldMbox : @SAWCorePrelude.Either unit (@sigT V64 (fun (len : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod (@Mbox) (prod (@SAWCorePrelude.BVVec 64 len BV64) unit))) -> @Mbox .

Axiom transMbox : @Mbox -> @Mbox -> @Mbox .

Definition foldBufs : forall (p0 : @SAWCorePrelude.Either unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)))), Mbox_def :=
  @foldMbox.

Definition unfoldBufs : forall (p0 : Mbox_def), let var__0   := @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool) in
  @SAWCorePrelude.Either unit (@sigT var__0 (fun (x_ex0 : var__0) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT var__0 (fun (x_ex1 : var__0) => unit))) unit))) :=
  @unfoldMbox.

Definition transBufs : forall (p0 : Mbox_def), forall (p1 : Mbox_def), Mbox_def :=
  @transMbox.

Definition clearbufs__tuple_fun : @CompM.lrtTupleType (@CompM.LRT_Cons (@CompM.LRT_Fun Mbox_def (fun (perm0 : Mbox_def) => @CompM.LRT_Ret Mbox_def)) (@CompM.LRT_Nil)) :=
  @CompM.multiFixM (@CompM.LRT_Cons (@CompM.LRT_Fun Mbox_def (fun (perm0 : Mbox_def) => @CompM.LRT_Ret Mbox_def)) (@CompM.LRT_Nil)) (fun (clearbufs : @CompM.lrtToType (@CompM.LRT_Fun Mbox_def (fun (perm0 : Mbox_def) => @CompM.LRT_Ret Mbox_def))) => pair (fun (p0 : Mbox_def) => @CompM.letRecM (@CompM.LRT_Cons (@CompM.LRT_Fun Mbox_def (fun (p1 : Mbox_def) => @CompM.LRT_Fun Mbox_def (fun (p2 : Mbox_def) => @CompM.LRT_Ret Mbox_def))) (@CompM.LRT_Nil)) Mbox_def (fun (f : @CompM.lrtToType (@CompM.LRT_Fun Mbox_def (fun (p1 : Mbox_def) => @CompM.LRT_Fun Mbox_def (fun (p2 : Mbox_def) => @CompM.LRT_Ret Mbox_def)))) => pair (fun (p1 : Mbox_def) (p2 : Mbox_def) => @SAWCorePrelude.either unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) (CompM Mbox_def) (fun (x_left0 : unit) => (fun (catchpoint : CompM Mbox_def) => @SAWCorePrelude.either unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) (CompM Mbox_def) (fun (x_left1 : unit) => @returnM CompM _ Mbox_def (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt))) (fun (x_right0 : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) => catchpoint) (@unfoldBufs p1)) (@returnM CompM _ Mbox_def (@transBufs p1 (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt))))) (fun (x_right0 : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) => @SAWCorePrelude.maybe (@SAWCoreScaffolding.Eq (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvult 64 (intToBv 64 0%Z) (@projT1 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0)) (@SAWCoreScaffolding.true)) (CompM Mbox_def) (@errorM CompM _ Mbox_def "0 <u ghost5"%string) (fun (ult_pf0 : @SAWCoreScaffolding.Eq (@SAWCoreScaffolding.Bool) (@SAWCoreVectorsAsCoqVectors.bvult 64 (intToBv 64 0%Z) (@projT1 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0)) (@SAWCoreScaffolding.true)) => (fun (catchpoint : CompM Mbox_def) => (fun (catchpoint1 : CompM Mbox_def) => @SAWCorePrelude.either unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) (CompM Mbox_def) (fun (x_left0 : unit) => f (@transBufs p1 (@foldBufs (@SAWCorePrelude.Right unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) (@existT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) (@projT1 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0) (pair (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt)) (pair (@SAWCorePrelude.adjustBVVec 64 (@projT1 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0) (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd (@projT2 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0))) (fun (fld0 : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) => @existT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit) (intToBv 64 0%Z) tt) (intToBv 64 0%Z)) tt)))))) (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt))) (fun (x_right1 : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) => catchpoint1) (@unfoldBufs (SAWCoreScaffolding.fst (@projT2 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0)))) (f (@transBufs p1 (@foldBufs (@SAWCorePrelude.Right unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) (@existT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) (@projT1 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0) (pair (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt)) (pair (@SAWCorePrelude.adjustBVVec 64 (@projT1 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0) (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd (@projT2 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0))) (fun (fld0 : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) => @existT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit) (intToBv 64 0%Z) tt) (intToBv 64 0%Z)) tt)))))) (@transBufs (SAWCoreScaffolding.fst (@projT2 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0)) (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt))))) (@SAWCorePrelude.either unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) (CompM Mbox_def) (fun (x_left0 : unit) => f (@transBufs p1 (@foldBufs (@SAWCorePrelude.Right unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) (@existT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) (@projT1 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0) (pair (@transBufs (SAWCoreScaffolding.fst (@projT2 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0)) (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt))) (pair (@SAWCorePrelude.adjustBVVec 64 (@projT1 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0) (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) (SAWCoreScaffolding.fst (SAWCoreScaffolding.snd (@projT2 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0))) (fun (fld0 : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit)) => @existT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit) (intToBv 64 0%Z) tt) (intToBv 64 0%Z)) tt)))))) (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt))) (fun (x_right1 : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) => @errorM CompM _ Mbox_def "
  Could not prove
    (z9, z8).
      top1:Bufs<z8>, local2:ptr((W,0) |-> eq(z8)),
      z9:llvmframe [local2:8], z8:Bufs<LLVMword 0>

  proveEq: Could not prove ghost4 = (z9, z8). LLVMword 0

  --------------------

  proveEq: Could not prove ghost4 = (z10, z9). ghost7

  --------------------

  proveEq: Could not prove top1 = (z10, z9). LLVMword 0

  --------------------

  proveEq: Could not prove top1 = (z11, z10). ghost7

  --------------------

  proveEq: Could not prove ghost4 = (z9, z8). LLVMword 0

  --------------------

  proveEq: Could not prove ghost4 = (z10, z9). ghost7

  --------------------

  proveEq: Could not prove ghost7 = (z14, z13). LLVMword 0

  --------------------

  proveVarImplH: Could not prove
  z12:eq(LLVMword 0)
  -o
  (z15, z14, z13).
    ptr((W,0) |-> Bufs<LLVMword 0>)
      *ptr((W,8) |-> eq(LLVMword z13))
      *array(16, <z13, *8, [(W,0) |-> int64<>], [])

  --------------------

  proveVarImplH: Could not prove
  ghost7:eq(LLVMword 0)
  -o
  (z15, z14, z13).
    ptr((W,0) |-> Bufs<LLVMword 0>)
      *ptr((W,8) |-> eq(LLVMword z13))
      *array(16, <z13, *8, [(W,0) |-> int64<>], [])

  --------------------

  proveEq: Could not prove LLVMword 0 = (z12, z11, z10). ghost7

  --------------------

  proveVarImplH: Could not prove
  z8:eq(LLVMword 0)
  -o
  (z12, z11, z10, z9).
    ptr((W,0) |-> Bufs<z11>)
      *ptr((W,8) |-> eq(LLVMword z9))
      *array(16, <z9, *8, [(W,0) |-> int64<>], [])"%string) (@unfoldBufs (SAWCoreScaffolding.fst (@projT2 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0))))) (@SAWCorePrelude.bvultWithProof 64 (intToBv 64 0%Z) (@projT1 (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_elimEx0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_elimEx0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit)) x_right0))) (@unfoldBufs p2)) tt) (fun (f : @CompM.lrtToType (@CompM.LRT_Fun Mbox_def (fun (p1 : Mbox_def) => @CompM.LRT_Fun Mbox_def (fun (p2 : Mbox_def) => @CompM.LRT_Ret Mbox_def)))) => (fun (catchpoint : CompM Mbox_def) => (fun (catchpoint1 : CompM Mbox_def) => @SAWCorePrelude.either unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) (CompM Mbox_def) (fun (x_left0 : unit) => f (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt)) (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt))) (fun (x_right0 : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) => catchpoint1) (@unfoldBufs p0)) (f (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt)) (@transBufs p0 (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt))))) (@SAWCorePrelude.either unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) (CompM Mbox_def) (fun (x_left0 : unit) => f (@transBufs p0 (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt))) (@foldBufs (@SAWCorePrelude.Left unit (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) tt))) (fun (x_right0 : @sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex0 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => prod Mbox_def (prod (@SAWCorePrelude.BVVec 64 x_ex0 (@sigT (@SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) (fun (x_ex1 : @SAWCoreVectorsAsCoqVectors.Vec 64 (@SAWCoreScaffolding.Bool)) => unit))) unit))) => @errorM CompM _ Mbox_def "
  Could not prove
    (z6, z5).
      top1:Bufs<z5>, local2:ptr((W,0) |-> eq(z5)),
      z6:llvmframe [local2:8], z5:Bufs<LLVMword 0>

  proveEq: Could not prove top1 = (z9, z8). LLVMword 0

  --------------------

  proveVarImplH: Could not prove
  z7:eq(LLVMword 0)
  -o
  (z10, z9, z8).
    ptr((W,0) |-> Bufs<LLVMword 0>)
      *ptr((W,8) |-> eq(LLVMword z8))
      *array(16, <z8, *8, [(W,0) |-> int64<>], [])

  --------------------

  proveVarImplH: Could not prove
  top1:eq(LLVMword 0)
  -o
  (z10, z9, z8).
    ptr((W,0) |-> Bufs<LLVMword 0>)
      *ptr((W,8) |-> eq(LLVMword z8))
      *array(16, <z8, *8, [(W,0) |-> int64<>], [])

  --------------------

  proveEq: Could not prove LLVMword 0 = (z8, z7). top1

  --------------------

  proveVarImplH: Could not prove
  z5:eq(LLVMword 0)
  -o
  (z8, z7, z6).
    ptr((W,0) |-> Bufs<z7>)
      *ptr((W,8) |-> eq(LLVMword z6))
      *array(16, <z6, *8, [(W,0) |-> int64<>], [])"%string) (@unfoldBufs p0)))) tt).

Definition clearbufs : @CompM.lrtToType (@CompM.LRT_Fun Mbox_def (fun (perm0 : Mbox_def) => @CompM.LRT_Ret Mbox_def)) :=
  SAWCoreScaffolding.fst clearbufs__tuple_fun.

End clearbufs.
