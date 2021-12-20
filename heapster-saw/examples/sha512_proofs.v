From Coq          Require Import Program.Basics.
From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Import SAWCorePrelude.

Require Import Examples.sha512_gen.
Import SHA512.

Definition sha512_block_data_order_precond num := isBvslt 64 (intToBv 64 0) num.

Lemma no_errors_sha512_block_data_order :
  refinesFun sha512_block_data_order
             (fun num _ _ => assumingM (sha512_block_data_order_precond num) noErrorsSpec).
Proof.
  unfold sha512_block_data_order, sha512_block_data_order__tuple_fun.
Admitted.
