From Coq          Require Import Init.Nat.
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From Records      Require Import Records.

From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.

Theorem rewrite_addNat m n : addNat m n = m + n.
Proof.
  induction m.
  { reflexivity. }
  {
    simpl.
    intuition.
  }
Defined.
