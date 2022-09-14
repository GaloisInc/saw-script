From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.
Import CompMExtraNotation. (*Open Scope fun_syntax2.*)

Declare Scope fun_syntax2.




  Infix "&&" := SAWCoreScaffolding.and : fun_syntax2.
  Infix "<=" := (SAWCoreVectorsAsCoqVectors.bvsle _) : fun_syntax2.
  Notation " a <P b" := (SAWCorePrelude.bvultWithProof _ a b) (at level 98) : fun_syntax2.
  Notation " a == b" := (SAWCorePrelude.bvEq _ a b) (at level 100) : fun_syntax2.
  Notation " a < b" := (SAWCoreVectorsAsCoqVectors.bvult _ a b) (at level 70) : fun_syntax2.

  Notation "( x ) [ bits ]" := (SAWCoreVectorsAsCoqVectors.intToBv bits x) : fun_syntax2.
  Notation "'If' m 'As' x 'Then' f 'Else' default " := (SAWCorePrelude.maybe _ _ default (fun x => f) m) (at level 100) : fun_syntax2.
  Notation "'If' m 'Then' f 'Else' default " := (SAWCorePrelude.maybe _ _ default (fun _ => f) m) (at level 99) : fun_syntax2.
  Notation "v [ ix <- elem ]" := (SAWCorePrelude.updBVVec _ _ _ v ix elem) (at level 100) : fun_syntax2.
  Infix "+" := (SAWCoreVectorsAsCoqVectors.bvAdd _) : fun_syntax2.
  Notation "'Forall' x : T , f" := (LRT_Fun T (fun x => f)) (at level 100, format " 'Forall'  x : T ,  '/ ' f") : fun_syntax2.
  Notation "T ->> f" := (LRT_Fun T (fun _ => f)) (at level 99, right associativity, format "T '/'  ->>  '/' f") : fun_syntax2.
  Notation "x" := (LRT_Ret x) (at level 99, only printing) : fun_syntax2.
  Notation "'Vector' T len":= (SAWCorePrelude.BVVec _ len T) (at level 98) : fun_syntax2.
  Notation "[[ x1 ]]":= ((LRT_Cons x1 LRT_Nil )) (at level 7,  format "[[ '[' x1 ']' ]]") : fun_syntax2.
  Notation "[[ x1 ; x2 ; .. ; xn ]]":= ((LRT_Cons x1 (LRT_Cons x2 .. (LRT_Cons xn LRT_Nil) .. )))
                                         (at level 7, format "[[ '[' x1 ; '/' x2 ; '/' .. ; '/' xn ']' ]]") : fun_syntax2.
  Notation "[ x1 ]__lrt":= (lrtTupleType (LRT_Cons x1 LRT_Nil )) (at level 7, format "[ '[' x1 ']' ]__lrt") : fun_syntax2.
  Notation "[ x1 ; x2 ; .. ; xn ]__lrt":= (lrtTupleType (LRT_Cons x1 (LRT_Cons x2 .. (LRT_Cons xn LRT_Nil) .. )))
                                            (at level 7, format "[ '[' x1 ; '/' x2 ; '/' .. ; '/' xn ']' ]__lrt") : fun_syntax2.
  Notation "'int64'" := (SAWCoreVectorsAsCoqVectors.bitvector 64) (at level 97) : fun_syntax2.
  Notation "'int32'" := (SAWCoreVectorsAsCoqVectors.bitvector 32)  (at level 97) : fun_syntax2.
  Notation "'bool'" := (SAWCoreVectorsAsCoqVectors.bitvector 1) (at level 97) : fun_syntax2.
  Notation "[ x ]__ty" := (lrtToType x) (only printing) : fun_syntax2.
  Notation "'LetRec'  x := f 'InBody' ( body )" := (letRecM _ (fun x => f) (fun x => body))
                                                     (at level 0, only printing,
                                                       format "'[ ' 'LetRec'  x := '//' '[' f ']' '//'  'InBody'  '/' ( '[' body ']' ) ']'") : fun_syntax2.
Notation "x" := (letRecM LRT_Nil tt x)
                     (at level 99, only printing) : fun_syntax2.
  Notation "[Functions: f1 := f1_body ]"  := (multiFixM  (fun f1 => (f1_body, tt)))
  (at level 100, only printing, format "[Functions: '//' f1  :=  '[' f1_body ']' ]") : fun_syntax2.
  Notation "[Functions: f1 := f1_body f2 := f2_body ]"  := (multiFixM (fun f1 f2 => (f1_body, f2_body, tt)))
  (at level 100, only printing, format "[Functions: '//' f1  :=  '[' f1_body ']' '//' f2  :=  '[' f2_body ']' ]") : fun_syntax2.
  
Delimit Scope fun_syntax2 with sytx.

Require Import Examples.tutorial_c_gen.
Import tutorial_c.

Lemma no_errors_add
  : refinesFun add (fun _ _ => noErrorsSpec).
Proof.
  
  unfold add, add__tuple_fun.
  Open Scope fun_syntax2.
  (* Visually simplifies trivial letRecM*)
  
  
  simpl.
  Notation 
  
  noErrorsSpec.
   
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
