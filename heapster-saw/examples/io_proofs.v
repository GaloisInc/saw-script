From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import SpecMExtra.
From EnTree       Require Import Automation.
Import SAWCorePrelude.
Import SpecMNotations.
Local Open Scope entree_scope.

Require Import Examples.io_gen.
Import io.

Print hello_world__bodies.
Print __x1_write.
