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


Lemma no_errors_is_elem : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun, noErrorsSpec,
         list_64_drop_in_place, _ZN5alloc5alloc8box_free17hc52ecccd139e11ceE,
         llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64.
  time "no_errors_is_elem" prove_refinement.
Qed.

Definition is_elem_fun' : bitvector 64 -> List_IRT (bitvector 64) ->
                          CompM (unit * bitvector 1) :=
  multiArgFixM
    (LRT_Fun (bitvector 64)
             (fun _ => LRT_Fun _ (fun _ => LRT_Ret (unit * bitvector 1))))
    (fun is_elem x l =>
       either
         _ _ _
         (fun _ => returnM (tt, intToBv 1 0))
         (fun arg =>
            let y := fst (snd arg) in
            let l' := fst (snd (snd arg)) in
            if bvEq 64 y x then returnM (tt, intToBv 1 1) else is_elem x l')
         (unfoldList_IRT _ l)).

Definition is_elem_fun : bitvector 64 -> List_IRT (bitvector 64) ->
                         CompM (unit * bitvector 1) :=
  fst
    (multiFixM
       (lrts := LRT_Cons (LRT_Fun _ (fun _ => LRT_Fun _ (fun _ => LRT_Ret _))) LRT_Nil)
       (fun is_elem =>
          (fun x l =>
             either
               _ _ _
               (fun _ => returnM (tt, intToBv 1 0))
               (fun arg =>
                  let y := fst (snd arg) in
                  let l' := fst (snd (snd arg)) in
                  if bvEq 64 y x then returnM (tt, intToBv 1 1) else is_elem x l')
               (unfoldList_IRT _ l), tt))).

Definition is_elem_fun2 : bitvector 64 -> List_IRT (bitvector 64) ->
                          CompM (unit * bitvector 1) :=
  fun x l =>
    letRecM
      (LRT_Cons (LRT_Fun _ (fun _ => LRT_Fun _ (fun _ => LRT_Ret _))) LRT_Nil)
      (fun is_elem =>
         (fun x l =>
            either
              _ _ _
              (fun _ => returnM (tt, intToBv 1 0))
              (fun arg =>
                 let y := fst (snd arg) in
                 let l' := fst (snd (snd arg)) in
                 if bvEq 64 y x then returnM (tt, intToBv 1 1) else is_elem x l')
              (unfoldList_IRT _ l), tt))
      (fun is_elem => is_elem x l).

Lemma is_elem_fun_ref : refinesFun is_elem is_elem_fun2.
Proof.
  unfold is_elem, is_elem__tuple_fun, noErrorsSpec,
         list_64_drop_in_place, _ZN5alloc5alloc8box_free17hc52ecccd139e11ceE,
         llvm__x2ememcpy__x2ep0i8__x2ep0i8__x2ei64, is_elem_fun.
  time "is_elem_fun_ref" prove_refinement.
Admitted.


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
