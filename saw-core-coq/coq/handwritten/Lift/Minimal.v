From Ornamental Require Import Ornaments.

Set DEVOID search prove equivalence.
Set DEVOID lift type.

Module SCS.
  Definition fst {A B} := @fst A B.
  Definition snd {A B} := @snd A B.
End SCS.

Module SN.

  Definition h : Type := (bool * nat).

  Definition c : Type := (nat * (nat * (bool * ((bool * nat) * nat)))).

  Definition f (h : h) (c : c) : bool :=
    andb (fst h) (fst (snd (snd c))).

End SN.

Preprocess Module SN as SN_PP { opaque andb }.

Module H.

  Record H :=
    {
      b : bool;
      n : nat;
    }.

  Scheme Induction for H Sort Prop.
  Scheme Induction for H Sort Type.
  Scheme Induction for H Sort Set.

  (* We'd like to wrap the ugly access into this: *)
  Definition get_h_b (h : SN.h) : bool := fst h.

End H.

Preprocess Module H as H_PP.

Lift SN_PP.h H_PP.H in H_PP.get_h_b as getHB.
Lift SN_PP.h H_PP.H in SN_PP.f as f_PP { opaque andb }.

Definition get_h_b_expected (h : SN_PP.h) :=
  Prod.fst _ _ h.

Arguments SN_PP.Coq_Init_Datatypes_fst [A B].
Arguments SN_PP.Coq_Init_Datatypes_snd [A B].

Notation "'fst_PP' x" := (SN_PP.Coq_Init_Datatypes_fst x) (at level 50, only printing).
Notation "'snd_PP' x" := (SN_PP.Coq_Init_Datatypes_snd x) (at level 50, only printing).

Print f_PP.

Definition f_PP_expected (h : H_PP.H) (c : nat * (nat * (bool * (H_PP.H * nat)))) : bool :=
 H_PP.b h
 &&
 SN_PP.Coq_Init_Datatypes_fst bool (H_PP.H * nat)
   (SN_PP.Coq_Init_Datatypes_snd nat (bool * (H_PP.H * nat))
                                 (SN_PP.Coq_Init_Datatypes_snd nat (nat * (bool * (H_PP.H * nat))) c)).

Lemma test_f_PP:
  f_PP = f_PP_expected.
Proof.
  unfold f_PP, f_PP_expected.
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => idtac
  end.
Qed.

Print f_PP.

(*
Output:

f_PP =
fun (h : H_PP.H) (c : nat * (nat * (bool * (H_PP.H * nat)))) =>
(H_PP.H_rect (fun _ : H_PP.H => bool) (fun (b : bool) (_ : nat) => b) h &&
 prod_rect (fun _ : bool * (H_PP.H * nat) => bool) (fun (a : bool) (_ : H_PP.H * nat) => a)
   (prod_rect (fun _ : nat * (bool * (H_PP.H * nat)) => (bool * (H_PP.H * nat))%type)
      (fun (_ : nat) (b : bool * (H_PP.H * nat)) => b)
      (prod_rect (fun _ : nat * (nat * (bool * (H_PP.H * nat))) => (nat * (bool * (H_PP.H * nat)))%type)
         (fun (_ : nat) (b : nat * (bool * (H_PP.H * nat))) => b) c)))%bool
     : H_PP.H -> nat * (nat * (bool * (H_PP.H * nat))) -> bool

Ideally, I'd love to have:

 *)

Definition f_PP_ideal
  : H_PP.H -> nat * (nat * (bool * (H_PP.H * nat))) -> bool
  := fun h c => (getHB h && (fst (snd (snd c))))%bool.

(*
Two differences:

- [H_PP.H_rect (fun _ : H_PP.H => bool) (fun (b : bool) (_ : nat) => b) h] is replaced with
   the lifted accessor [getHB].

- The other calls to [fst] and [snd] are somehow magically preserved, while
  the calls that participate in the lifting have been properly replaced.  This
  is hard, not sure how you can make it so smart...

 *)

Module C.

  Record C :=
    {
      n1 : nat;
      n2 : nat;
      b  : bool;
      h  : H_PP.H;
      n3 : nat;
    }.

  (* We'd like to wrap the ugly access into this: *)
  Definition get_c_b (c : SN.c) : bool := fst (snd (snd c)).

  Scheme Induction for C Sort Prop.
  Scheme Induction for C Sort Type.
  Scheme Induction for C Sort Set.

End C.

Preprocess Module C as C_PP.

Lift SN_PP.h H_PP.H in SN_PP.c as c_PP.

Lift SN_PP.h H_PP.H in C_PP.get_c_b as getCB0.
Lift c_PP C_PP.C in getCB0 as getCB.

Lift SN_PP.h H_PP.H in SN_PP.f as f0 { opaque andb }.

(* oh this is nice! f0 is defined to be f_PP! *)

Lift c_PP C_PP.C in f0 as f { opaque andb }.

Print f.

(*
  Output:

f =
fun (h : H_PP.H) (c : C_PP.C) =>
(H_PP.H_rect (fun _ : H_PP.H => bool) (fun (b : bool) (_ : nat) => b) h &&
 prod_rect (fun _ : bool * (H_PP.H * nat) => bool) (fun (a : bool) (_ : H_PP.H * nat) => a)
   (prod_rect (fun _ : nat * (bool * (H_PP.H * nat)) => (bool * (H_PP.H * nat))%type)
      (fun (_ : nat) (b : bool * (H_PP.H * nat)) => b)
      (C_PP.C_rect (fun _ : C_PP.C => (nat * (bool * (H_PP.H * nat)))%type)
         (fun (_ n2 : nat) (b : bool) (h0 : H_PP.H) (n3 : nat) => (n2, (b, (h0, n3)))) c)))%bool
     : H_PP.H -> C_PP.C -> bool

This has the type that I want, but the body of the function is a little too
verbose, due to calls to [fst] and [snd] not being opaque, and having been
replaced with the more verbose [prod_rect].

Ideally I'd love:

 *)

Definition f' (h : H_PP.H) (c : C_PP.C)
  : bool
  := (getHB h && getCB c)%bool.
