(* This file contains definitions that seemed missing from Coq.Vectors.Vector *)

From Stdlib         Require Import PeanoNat.
From Stdlib.Vectors Require Vector.

Fixpoint zip {a b : Type} {n : nat} (xs : Vector.t a n) (ys : Vector.t b n) : Vector.t (a * b) n.
  refine (
    match
      xs in Vector.t _ n'
      return Vector.t _ n' -> Vector.t _ n'
    with
    | Vector.nil _ => fun _ => Vector.nil _
    | Vector.cons _ x pn xs =>
      fun ys =>
        match
          ys in Vector.t _ n'
          return S pn = n' -> Vector.t _ n'
        with
        | Vector.nil _ => fun absurd => False_rect _ (Nat.neq_succ_0 _ absurd)
        | Vector.cons _ y pn' ys =>
          fun eq =>
            let xs' := eq_rect _ _ xs _ (eq_add_S _ _ eq) in
            Vector.cons _ (x, y) pn' (zip _ _ _ xs' ys)
        end eq_refl
    end ys
    ).
Defined.
