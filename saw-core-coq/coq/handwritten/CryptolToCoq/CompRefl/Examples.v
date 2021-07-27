
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
  unshelve eapply (check_refinesFun_sound _ _ _); try exact [];
  [ prove_closed | prove_closed | ];
  compute - [goalD]; cbn;
  repeat (intro || apply split_and).


Let ex1_fmt := FunMT (EitherT (TypeT 0) (TypeT 0)) (CompMT (TypeT 0)).
Let ex1_fme1 : fmexpr [unit] ex1_fmt :=
  fun n => eitherE _ _ (fun m => returnE _ _ (varE _ m))
                       (fun m => returnE _ _ (varE _ m))
                       (varE _ n).
Let ex1_fme2 : fmexpr [unit] ex1_fmt :=
  fun _ => returnE _ _ (termE [unit] 0 tt).

Example ex1 :
  @refinesFun (LRT_Fun (SAWCorePrelude.Either unit unit) (fun _ => LRT_Ret unit))
              (fun x => SAWCorePrelude.either _ _ _ returnM returnM x)
              (fun _ => returnM tt).
Proof.
  change (LRT_Fun (SAWCorePrelude.Either unit unit) (fun _ => LRT_Ret unit))
    with (fmtypeD [unit] ex1_fmt); unfold ex1_fmt.
  change (fun x => SAWCorePrelude.either _ _ _ returnM returnM x)
    with (fmexprD [unit] Ctx.empty ex1_fme1); unfold ex1_fme1.
  change (fun _ => returnM tt)
    with (fmexprD [unit] Ctx.empty ex1_fme2); unfold ex1_fme2.
  prove_refinesFun.
  - destruct x0; reflexivity.
  - destruct x0; reflexivity.
Qed.
