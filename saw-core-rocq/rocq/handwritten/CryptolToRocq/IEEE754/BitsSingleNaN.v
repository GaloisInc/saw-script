(**
 * This is an adaptation of IEEE754.Bits from the Flocq library that works
 * over BinarySingleNaN (i.e., a IEEE-754 floating-point type with a single,
 * distinguished NaN value) instead of Binary (which permits multiple, distinct
 * NaN values). Arguably, this should be upstreamed into Flocq itself.
 *)

From Stdlib Require Import ZArith Reals Psatz SpecFloat.

From Flocq Require Import Core Round Bracket Operations Div Sqrt Relative BinarySingleNaN.

From Flocq Require Binary Bits.

Section Binary_Bits.

(** Number of bits for the fraction and exponent *)
Variable mw ew : positive.

Let prec := Z.pos (Pos.succ mw).
Let emax := Zpower 2 (Z.pos ew - 1).
Notation binary_float := (binary_float prec emax) (only parsing).

Hypothesis Hmax : (1 < emax)%Z.

Definition bits_of_binary_float (nan : { nan : Binary.binary_float prec emax | Binary.is_nan prec emax nan = true }) (x : binary_float) : Z :=
  Bits.bits_of_binary_float mw ew (Binary.BSN2B prec emax nan x).

Definition bits_of_binary_float' (x : binary_float) (Nx : is_nan x = false) : Z :=
  Bits.bits_of_binary_float mw ew (Binary.BSN2B' prec emax x Nx).

Definition split_bits_of_binary_float (nan : { nan : Binary.binary_float prec emax | Binary.is_nan prec emax nan = true
}) (x : binary_float) : bool * Z * Z :=
  Bits.split_bits_of_binary_float mw ew (Binary.BSN2B prec emax nan x).

Definition split_bits_of_binary_float' (x : binary_float) (Nx : is_nan x = false) : bool * Z * Z :=
  Bits.split_bits_of_binary_float mw ew (Binary.BSN2B' prec emax x Nx).

Definition binary_float_of_bits (x : Z) : binary_float :=
  Binary.B2BSN prec emax (Bits.binary_float_of_bits mw ew Hmax x).

End Binary_Bits.
