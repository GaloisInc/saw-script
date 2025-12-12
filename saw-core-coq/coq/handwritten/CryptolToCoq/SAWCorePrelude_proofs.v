From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Morphisms.
From Stdlib Require Import String.
#[local] Set Warnings "-stdlib-vector".
From Stdlib Require Import Vectors.Vector.
#[local] Set Warnings "stdlib-vector".

From mathcomp Require Import eqtype.
From mathcomp Require Import ssrbool.
From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrnat.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

Import ProperNotations.
Import SAWCorePrelude.

Global Instance Proper_gen n a :
    Proper (@pointwise_relation _ _ eq ==> eq) (@gen n a).
Proof.
  induction n.
  {
    now simpl.
  }
  {
    intros f g FG.
    simpl.
    f_equal.
    {
      now apply FG.
    }
    {
      setoid_rewrite IHn.
      {
        reflexivity.
      }
      {
        intro.
        apply FG.
      }
      {
        constructor.
      }
    }
  }
Qed.

Global Instance Proper_genOrdinal n a :
    Proper (@pointwise_relation _ _ eq ==> eq) (@genOrdinal n a).
Proof.
  induction n.
  {
    now simpl.
  }
  {
    intros f g FG.
    simpl.
    f_equal.
    {
      now apply FG.
    }
    {
      setoid_rewrite IHn.
      {
        reflexivity.
      }
      {
        intro.
        apply FG.
      }
      {
        constructor.
      }
    }
  }
Qed.

Global Instance Proper_Nat__rec p T :
    Proper
      (
        (forall_relation (fun _ => eq ==> eq)%signature)
          ==>
          (forall_relation (fun _ => eq))
      )
      (@Nat__rec p T).
Proof.
  intros tSucc1 tSucc2 TSucc n.
  induction n.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    now erewrite TSucc.
  }
Qed.

Theorem rewrite_addNat m n : addNat m n = m + n.
Proof.
  induction m.
  { reflexivity. }
  {
    simpl.
    rewrite IHm.
    intuition.
  }
Defined.

Theorem sawAt_zero T size h t :
    sawAt (S size) T (Vector.cons T h size t) 0 = h.
Proof.
  unfold sawAt. now simpl.
Qed.

Theorem sawAt_S T size h t index :
    sawAt (S size) T (Vector.cons T h size t) (S index) = sawAt size T t index.
Proof.
  unfold sawAt. now simpl.
Qed.

Lemma gen_sawAt T {HT : Inhabited T}
  : forall (m : nat) a, gen m T (fun i => sawAt m T a i) = a.
Proof.
  apply Vector.t_ind.
  {
    simpl.
    reflexivity.
  }
  {
    move => h n t IH.
    simpl.
    f_equal.
    exact IH.
  }
Qed.

Lemma append_cons m n T {HT:Inhabited T} h t v
  : append m.+1 n T (Vector.cons T h m t) v
    =
    Vector.cons T h _ (append m n T t v).
Proof.
  reflexivity.
Qed.

Theorem rewrite_append T {HT:Inhabited T} n (w : Vec n T)
  : forall m (v : Vec m T),
    existT _ (addNat m n) (append m n T v w)
    =
    existT _ (m + n) (Vector.append v w).
Proof.
  apply Vector.t_ind.
  {
    simpl.
    f_equal.
    unfold append.
    rewrite gen_sawAt.
    reflexivity.
  }
  {
    simpl => h m t IH.
    rewrite append_cons.
    dependent rewrite IH.
    reflexivity.
  }
Qed.
