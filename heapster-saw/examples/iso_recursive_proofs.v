From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.iso_recursive.
Import iso_recursive.

Import SAWCorePrelude.

Ltac list_IRT_destruct l l' := destruct l as [| ? l'].
Ltac list_IRT_induction l l' := induction l as [| ? l'].
Ltac list_IRT_simpl := simpl unfoldList_IRT in *; simpl foldList_IRT in *.

Hint Extern 2 (IntroArg ?n (eq (unfoldList_IRT _ _ ?l)
                               (SAWCorePrelude.Left _ _ _)) _) =>
  doDestruction (list_IRT_destruct) (list_IRT_simpl) l : refinesFun.
Hint Extern 2 (IntroArg ?n (eq (unfoldList_IRT _ _ ?l)
                               (SAWCorePrelude.Right _ _ _)) _) =>
  doDestruction (list_IRT_destruct) (list_IRT_simpl) l : refinesFun.


Lemma no_errors_is_elem : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun, noErrorsSpec.
  time "no_errors_is_elem (IRT)" prove_refinement.
Qed.
