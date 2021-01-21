From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import SAWCorePrelude.

From mathcomp Require Import eqtype.
From mathcomp Require Import ssrnat.
From mathcomp Require Import tuple.

Scheme Minimality for tuple.tuple_of Sort Prop.
Scheme Induction  for tuple.tuple_of Sort Set.
Scheme Induction  for tuple.tuple_of Sort Type.

Scheme Minimality for eqtype.Equality.type Sort Prop.
Scheme Induction  for eqtype.Equality.type Sort Set.
Scheme Induction  for eqtype.Equality.type Sort Type.

Scheme Minimality for eqtype.Equality.mixin_of Sort Prop.
Scheme Induction  for eqtype.Equality.mixin_of Sort Set.
Scheme Induction  for eqtype.Equality.mixin_of Sort Type.

Scheme Induction for eqtype.Sub_spec Sort Prop.
Scheme Induction for eqtype.Sub_spec Sort Set.
Scheme Induction for eqtype.Sub_spec Sort Type.

Scheme Induction for eqtype.insub_spec Sort Prop.
Scheme Induction for eqtype.insub_spec Sort Set.
Scheme Induction for eqtype.insub_spec Sort Type.

Scheme Induction for eqtype.subType Sort Prop.
Scheme Induction for eqtype.subType Sort Set.
Scheme Induction for eqtype.subType Sort Type.

From Ornamental Require Import Ornaments.

Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)

Preprocess
  Module
  SAWCorePrelude
  as SAWCorePrelude'
       { opaque
           Coq.Init.Nat.pred
           Coq.Init.Nat.even
           SAWCoreScaffolding.error
           SAWCorePrelude.intToBv
           SAWCorePrelude.bvToInt
           mathcomp.ssreflect.eqtype.eq_irrelevance
           mathcomp.ssreflect.ssrnat.half
           CryptolPrimitives.seq
       } .
