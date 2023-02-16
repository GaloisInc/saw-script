(*
* Common definitions and tactics that make the examples easier to
* state and prove. Some or all of these could go into an automation file
* so we can start building functionality.  *)

From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SpecMExtra.
From EnTree  Require Import Automation.

Set Bullet Behavior "Strict Subproofs".


(* Spec when all events and returns are expected to be the same *)
Definition spec_refines_eq {E Γ R}:
  Rel (SpecM E Γ R) (SpecM E Γ R):=
  @spec_refines E E Γ Γ eqPreRel eqPostRel R R eq.

(* The spec fro things that have no errors. *)
Definition safety_spec {E Γ R A} {QT: QuantType R}: forall a: A, SpecM E Γ R:=
  total_spec (fun _ => True) (fun _ _ => True).


(** * Tactics for solving trivial spec refinement *)

(* unfolds the corresponding to the `fun__bodies` of a spec. *)
Ltac unfold_bodies:=
  match goal with |- context[MultiFixS _ _ _ ?X__bodies] => unfold X__bodies end.

(* | Unfolds a function applied to an arbitrary number of
arguments. Might fail if the function is a transparent definition of
an applied relation. *)
Ltac unfold_head T :=
  match T with
  | ?T _ => unfold_head T
  | ?T => unfold T; unfold_bodies
  end.

(* | Unfolds a function definition `func` and its body `func__bodies` *)
Ltac unfold_function:=
  try unfold spec_refines_eq, safety_spec;
  match goal with
  | |- spec_refines _ _ _ ?fun_applied _ =>
      let T:= fun_applied in
      unfold_head T
  end.

(* The follwoing functions are for automatically matching arguments,
   in a spec trivial spec *)
Ltac PreCase_conjunction x y:=
  eapply Logic.and;[exact (x=y)| ].

Ltac cont_join x tl cont:=
  match tl with
  | (?front, ?final) =>
      PreCase_conjunction x final; (cont front)
  | _ => exact (x = tl)
  end.

Ltac SubGoal ls1 ls2 cont:=
  match ls1 with
  | (?x0 ; ?tl1 ) =>  SubGoal tl1 ls2 ltac:(fun tl2 => cont_join x0 tl2 cont)
  | _ => cont ls2
  end.

(* Ltac for trivial PreCase *) 
Ltac PreCase_Trivial:=
  match goal with
    |- PreCase _ _ ?ls1 (?ls2; tt) =>
      SubGoal ls1 ls2 ltac:(fun ls => exact True) (* last part is only triggered if the lists are empty*)
  end.

(* Ltac for trivial PostCase *) 
Ltac list_zip ls1 ls2:=
  match ls1 with
  | (?x, ?ls1') => match ls2 with
                  | (?y, ?ls2') =>
                      apply Logic.and;
                      [list_zip ls1' ls2' | exact (x = y)]
                  | _ => fail "Mismatched lists"
                  end
  | _ => exact (ls1 = ls2)
  end.

Ltac PostCase_Trivial:=
  match goal with
    |- PostCase _ _ _ _ ?ls1 ?ls2  => list_zip ls1 ls2
  end.


Ltac solve_prepost_case n m:=
  prepost_case n m;
    [PreCase_Trivial
    | PostCase_Trivial
    | prepost_exclude_remaining].

(* | This tactic solves many trivial spec refinements, specially good
     when proving there is no error, which is generally trivial. *)
Ltac solve_trivial_spec n m:=
  intros; unfold_function; prove_refinement;
    [wellfounded_none |  solve_prepost_case n m| prove_refinement_continue].
