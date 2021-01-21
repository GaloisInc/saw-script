From Bits Require Import operations.
From Bits Require Import spec.

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Program.Equality.
From Coq Require Import Vector.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.

From S2N Require Import S2N.
From S2N Require Import Embedding.

From mathcomp Require Import eqtype.
From mathcomp Require Import fintype.
From mathcomp Require Import seq.
From mathcomp Require Import ssreflect.
From mathcomp Require Import ssrbool.
From mathcomp Require Import ssrnat.
From mathcomp Require Import tuple.

Import CryptolPrimitives.
Import ListNotations.
Import SAWCorePrelude.
Import VectorNotations.

Class Pointed T :=
  {
    pointed : T;
  }.

Global Instance Pointed_Bool : Pointed bool :=
  {| pointed := false; |}.

Global Instance Pointed_prod {A B} `{Pointed A} `{Pointed B}
  : Pointed (A * B)%type :=
  {| pointed := (pointed, pointed); |}.

Global Instance Pointed_tuple {T} `{Pointed T} {n} : Pointed (n.-tuple T) :=
  {| pointed := [tuple pointed | i < n]; |}.
