This repository contains the code for SAWCore, an intermediate
language for representing the semantics of software (and potentially
hardware). It provides support for constructing models in a
dependently-typed lambda-calculus, transforming those models using a
rewriting engine, concretely or symbolically interpreting those
models, and emitting them as input to various external theorem
provers.

Currently, the library supports generating AIG, CNF, and SMT-Lib
output.
