From Bits Require Import operations.
From Bits Require Import spec.

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Program.Equality.
From Coq Require Import Vector.

From CryptolToCoq Require Import Cryptol_proofs.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import S2N.

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

Class Embedding A B :=
  {
    toAbstract : A -> B;
    toConcrete : B -> A;
  }.

(**
Keeping [ProperEmbedding] separate allows computations that depend on
[Embedding] to go through even when we admit the proof of [ProperEmbedding].
 *)
Class ProperEmbedding {A B} `(Embedding A B) :=
  {
    roundtrip : forall a, toConcrete (toAbstract a) = a;
  }.

Global Instance Embedding_Bool
  : Embedding Bool bool :=
  {|
    toAbstract := fun b => b;
    toConcrete := fun b => b;
  |}.

Global Instance ProperEmbedding_Bool : ProperEmbedding Embedding_Bool.
Proof.
  constructor.
  reflexivity.
Defined.

Fixpoint seq_to_tuple {T} {n : nat} (s : seq n T) : n.-tuple T :=
  match s with
  | nil => [tuple]
  | cons h _ t => cat_tuple [tuple of [:: h]] (seq_to_tuple t)
  end.

Global Instance Embedding_seq_tuple A B (n : nat) `{Embedding A B}
  : Embedding (seq n A) (n.-tuple B) :=
  {|
    toAbstract c := map_tuple toAbstract (seq_to_tuple c);
    toConcrete b := genOrdinal _ _ (fun i => toConcrete (tnth b i));
  |}.

Global Instance Embedding_prod {A B C D} `{Embedding A B} `{Embedding C D}
  : Embedding (A * C) (B * D) :=
  {|
    toAbstract '(a, c) := (toAbstract a, toAbstract c);
    toConcrete '(b, d) := (toConcrete b, toConcrete d);
  |}.
