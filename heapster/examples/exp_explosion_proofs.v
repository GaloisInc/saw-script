From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.exp_explosion_gen.
Import exp_explosion.

Import SAWCorePrelude.

Lemma no_errors_explosion : refinesFun exp_explosion (fun _ => noErrorsSpec).
Proof.
  unfold exp_explosion, exp_explosion__tuple_fun, noErrorsSpec.
  time "no_errors_exp_explosion" prove_refinement.
Qed.
