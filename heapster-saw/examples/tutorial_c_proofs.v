From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

(* The following line enables pretty printing*)
Import CompMExtraNotation. Open Scope fun_syntax.

Require Import Examples.tutorial_c_gen.
Import tutorial_c.


Lemma no_errors_add
  : refinesFun add (fun _ _ => noErrorsSpec).
Proof.
  unfold add, add__tuple_fun.
  prove_refinement.
Qed.
  
Lemma no_errors_add_mistyped
  : refinesFun add_mistyped (fun _ => noErrorsSpec).
Proof.
  unfold add_mistyped, add_mistyped__tuple_fun, noErrorsSpec.
  prove_refinement. 
  (* Fails to solve the goal. *)
Abort.


Lemma no_errors_incr_ptr
  : refinesFun incr_ptr (fun _ => noErrorsSpec).
Proof.
  unfold incr_ptr, incr_ptr__tuple_fun, noErrorsSpec.
  prove_refinement.
Qed.
  
Lemma no_errors_norm_vector
  : refinesFun norm_vector (fun _ _ _ => noErrorsSpec).
Proof.
  unfold norm_vector, norm_vector__tuple_fun, noErrorsSpec.
  prove_refinement.
Qed.
