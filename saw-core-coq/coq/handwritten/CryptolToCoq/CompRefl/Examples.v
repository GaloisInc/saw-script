
From Coq          Require Import Lists.List.
From Coq          Require Import OrderedType.
From Coq          Require Import OrderedTypeEx.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import CompM.
From CryptolToCoq Require Import CompRefl.CompRefl.
From CryptolToCoq Require Import CompRefl.Reify.

Import ListNotations.



Lemma split_and {P Q : Prop} : P -> Q -> P /\ Q.
Proof. tauto. Qed.

Global Transparent Ctx.isFresh Ctx.empty Ctx.extWith Ctx.ext Ctx.find Ctx.mem.

Create HintDb mem_exts.
Hint Resolve Ctx.mem_extWith_1 Ctx.mem_extWith_2 Ctx.mem_ext_1 Ctx.mem_ext_2 : mem_exts.

Ltac prove_closed :=
  repeat (intro || apply split_and); simpl;
  (typeclasses eauto with mem_exts || reflexivity).

Ltac prove_refinesFun :=
  reifyFMExpr_refinesFun;
  unshelve eapply (check_refinesFun_sound _ _ _); try exact [];
  [ prove_closed | prove_closed | ];
  compute - [goalD]; simpl;
  repeat (intro || apply split_and); compute.


Inductive unit' : Set := tt'.

Example ex1 :
  @refinesFun (LRT_Fun (SAWCorePrelude.Either unit' unit') (fun _ => LRT_Ret unit'))
              (fun x => SAWCorePrelude.either _ _ _ returnM returnM x)
              (fun _ => returnM tt').
Proof.
  prove_refinesFun.
  - destruct x0; reflexivity.
  - destruct x0; reflexivity.
Qed.
