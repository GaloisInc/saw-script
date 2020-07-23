SAWCore is a purely functional dependently-typed intermediate language
for representing the semantics of software (and potentially hardware).
It includes primitive types and operations sufficient to represent
values from a multitude of languages, such as C, LLVM, Java, and
Cryptol.

This repository contains multiple Haskell packages:

  * **`saw-core`** defines the term language, the surface syntax with
      parser and type checker, a term rewriting engine, and various
      operations for constructing, analyzing, and evaluating terms.

  * **`saw-core-aig`** provides a backend for generating And-Inverter
      Graphs (AIGs) from SAWCore terms.

  * **`saw-core-sbv`** provides a backend for translating SAWCore
      terms into symbolic values in the Haskell SBV library, which can
      be sent to external SMT solvers.

  * **`saw-core-what4`** provides a backend for translating SAWCore
      terms into symbolic values in the Haskell What4 library, which
      can be send to external SMT solvers.
