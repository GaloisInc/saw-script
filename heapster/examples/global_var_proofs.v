From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.



Require Import Examples.global_var_gen.
Import GlobalVar.

Import SAWCorePrelude.

Lemma no_errors_acquire_release_acquire_release :
    refinesFun acquire_release_acquire_release (fun _ => noErrorsSpec).
Proof.
    unfold acquire_release_acquire_release,
           acquire_release_acquire_release__tuple_fun,
           noErrorsSpec,
           acquireLockM, releaseLockM.
    prove_refinement.
Qed.
    

Definition acquire_release_acquire_release_spec (x : bitvector 64)
    : CompM (can_lock_perm * bitvector 64) :=
    returnM (intToBv 64 42, intToBv 64 42).

Lemma spec_acquire_release_acquire_release :
        refinesFun acquire_release_acquire_release
                   acquire_release_acquire_release_spec.
Proof.
    unfold acquire_release_acquire_release,
           acquire_release_acquire_release__tuple_fun,
           acquire_release_acquire_release_spec,
           acquireLockM, releaseLockM,
           projT2.
    prove_refinement.
Qed.


Definition errorSpec {A} : CompM A := existsM (fun (s : string) => errorM s).

Lemma errors_acquire_release_fail : refinesFun acquire_release_fail
                                               (fun _ => errorSpec).
Proof.
    unfold acquire_release_fail, acquire_release_fail__tuple_fun,
           errorSpec,
           acquireLockM, releaseLockM,
           projT2.
    prove_refinement.
Qed.
    
