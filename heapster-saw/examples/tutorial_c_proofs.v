From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import SAWCorePrelude.

(* The following 2 lines enables pretty printing*)
From CryptolToCoq Require Import CompMExtra.
Import CompMExtraNotation. Open Scope fun_syntax.

(* The following 2 lines allows better automatio*)
Require Import Examples.common.
Require Import Coq.Program.Tactics.

Require Import Examples.tutorial_c_gen.
Import tutorial_c.

Lemma no_errors_add (x y: bitvector 64) :
  spec_refines_eq (add x y) (safety_spec (x,y)).
Proof. solve_trivial_spec 0 0. Qed.
   
Lemma no_errors_add_mistyped (x: bitvector 64) :
  spec_refines_eq (add_mistyped x) (safety_spec (x)).
Proof. solve_trivial_spec 0 0.

(* After rewriting the terms for clarity, you can see the
   remaining goal says that an `ErrorS` is a refinement of
   `RetS`. In other words, it's trying to prove that a trivially
   pure function has an error. That's obviously false. *)
      clarify_goal_tutorial.
Abort.

Lemma no_errors_incr_ptr (x: bitvector 64) :
  spec_refines_eq (incr_ptr x) (safety_spec x).
Proof.  solve_trivial_spec 0 0. Qed.
  
Lemma no_errors_norm_vector (x y z: bitvector 64) :
  spec_refines_eq (norm_vector x y z) (safety_spec (x, y, z)).
Proof. solve_trivial_spec 0 0.

       (* The remaining goal, is to show that if initial arguments are
       equal (for both specs) then at the end of the execution, they
       are also equal.*)
       destruct_conjs; subst; reflexivity.
Qed.
