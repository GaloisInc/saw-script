From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Require Import Examples.rust_data_gen.
Import rust_data.

Import SAWCorePrelude.

(* Print bool_and__tuple_fun. *)

(* Print test_result__tuple_fun. *)

(* Print test_sum_impl__tuple_fun. *)

(* Print list_is_empty__tuple_fun. *)

(* Print list_head__tuple_fun. *)

(* Print list_head_impl__tuple_fun. *)

(* Print str_struct_new__tuple_fun. *)

(* FIXME: need to handle mapBVVecM for this one to work!
Lemma no_errors_str_struct_new : refinesFun str_struct_new (fun _ _ _ _ => noErrorsSpec).
Proof.
  unfold str_struct_new, str_struct_new__tuple_fun, noErrorsSpec, llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64, to_string_str.
  prove_refinement.
Qed.

Definition str_struct_new_spec (len:bitvector 64) (_:unit)
           (str:BVVec 64 len (bitvector 8)) :
  CompM {len' : bitvector 64
                & (BVVec 64 len' (bitvector 8) * (bitvector 64 * unit))%type} :=
  returnM (existT (fun len' => (BVVec 64 len' (bitvector 8) * (bitvector 64 * unit))%type) len (str, (len, tt))).

Lemma str_struct_new_correct : refinesFun str_struct_new str_struct_new_spec.
Proof.
  unfold str_struct_new, str_struct_new__tuple_fun, noErrorsSpec, llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64, to_string_str.
  prove_refinement.
Qed.
*)
