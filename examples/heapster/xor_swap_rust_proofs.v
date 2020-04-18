
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From Records      Require Import Records.

From CryptolToCoq Require Import SAWCorePrelude.

Load "xor_swap_rust.v".
Import xor_swap_rust.

Definition noErrors {A} (m:CompM A) : Prop := (m None) -> False.

Lemma noErrors_returnM A (a:A) : noErrors (returnM a).
Proof.
  intro. discriminate H.
Qed.

Lemma noErrors_xor_swap x1 x2 : noErrors (xor_swap_rust x1 x2).
Proof.
  unfold xor_swap_rust; simpl.
  apply noErrors_returnM.
Qed.
