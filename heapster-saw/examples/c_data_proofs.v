From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.c_data_gen.
Import c_data.

Import SAWCorePrelude.

Lemma no_errors_incr_u64_ptr_byte :
  refinesFun incr_u64_ptr_byte (fun _ => noErrorsSpec).
  unfold incr_u64_ptr_byte, incr_u64_ptr_byte__tuple_fun, noErrorsSpec.
  time "no_errors_incr_u64_ptr_byte" prove_refinement.
Qed.

Lemma no_errors_alloc_padded_struct :
  refinesFun alloc_padded_struct noErrorsSpec.
  unfold alloc_padded_struct, alloc_padded_struct__tuple_fun, noErrorsSpec, malloc.
  time "no_errors_alloc_padded_struct" prove_refinement.
Qed.

Lemma no_errors_padded_struct_incr_all :
  refinesFun padded_struct_incr_all (fun _ => noErrorsSpec).
  unfold padded_struct_incr_all, padded_struct_incr_all__tuple_fun, noErrorsSpec.
  time "no_errors_padded_struct_incr_all" prove_refinement.
Qed.
