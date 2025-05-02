From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From EnTree  Require Import Automation.

Require Import Examples.common.
Require Import Examples.c_data_gen.
Import c_data.

Import SAWCorePrelude.


Set Bullet Behavior "Strict Subproofs".

Global Hint Unfold malloc: automation.

Lemma no_errors_incr_u64_ptr_byte x:
  spec_refines_eq (incr_u64_ptr_byte x) (safety_spec (x)).
Proof. solve_trivial_spec 0 0. Qed.

Lemma no_errors_alloc_padded_struct :
  spec_refines_eq alloc_padded_struct (safety_spec tt).
Proof. solve_trivial_spec 0 0; solve_trivial_sidecondition. Qed.
         
Lemma no_errors_padded_struct_incr_all x0:
  spec_refines_eq (padded_struct_incr_all x0) (safety_spec (x0)).
Proof. solve_trivial_spec 0 0; solve_trivial_sidecondition. Qed.
