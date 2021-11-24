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

Lemma no_errors_sha512_block_data_order_simpl1 :
  refinesFun sha512_block_data_order_simpl1 (fun _ _ _ => noErrorsSpec).
Proof.
  unfold sha512_block_data_order_simpl1, sha512_block_data_order_simpl1__tuple_fun.
  Set Printing Depth 1000.
