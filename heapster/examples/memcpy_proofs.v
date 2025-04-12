From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.memcpy_gen.
Import memcpy.

Import SAWCorePrelude.


Lemma no_errors_copy_int : refinesFun copy_int (fun _ => noErrorsSpec).
Proof.
  unfold copy_int, copy_int__tuple_fun, noErrorsSpec, llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64.
  prove_refinement.
Qed.

Lemma no_errors_copy_ptr_contents : refinesFun copy_ptr_contents (fun _ => noErrorsSpec).
Proof.
  unfold copy_ptr_contents, copy_ptr_contents__tuple_fun, noErrorsSpec, llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64.
  prove_refinement.
Qed.

Lemma no_errors_copy_ptr : refinesFun copy_ptr (fun _ => noErrorsSpec).
Proof.
  unfold copy_ptr, copy_ptr__tuple_fun, noErrorsSpec, llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64.
  prove_refinement.
Qed.
