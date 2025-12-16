# Overview

The Software Analysis Workbench (SAW) is a tool for constructing
mathematical models of the computational behavior of software,
transforming these models, and proving properties about them.

SAW can currently construct models of a subset of programs written in
Cryptol, LLVM (and therefore C), JVM byte code (and therefore Java),
and MIR (and therefore Rust). The
models take the form of typed functional programs, so in a sense SAW can
be considered a translator from imperative programs to their functional
equivalents. Various external proof tools, including a variety of SAT
and SMT solvers, can be used to prove properties about the functional
models. SAW can construct models from arbitrary Cryptol programs, and
from C and Java programs that have fixed-size inputs and outputs and
that terminate after a fixed number of iterations of any loop (or a
fixed number of recursive calls). One common use case is to verify that
an algorithm specification in Cryptol is equivalent to an algorithm
implementation in C or Java.

The process of extracting models from programs, manipulating them,
forming queries about them, and sending them to external provers is
orchestrated using a special purpose language called SAWScript.
SAWScript is a typed functional language with support for sequencing of
imperative commands.

The rest of this document first describes how to use the SAW tool,
`saw`, and outlines the structure of the SAWScript language and its
relationship to Cryptol. It then presents the SAWScript commands that
transform functional models and prove properties about them. Finally, it
describes the specific commands available for constructing models from
imperative programs.

## SAW Use Cases

:::{warning}
This section is under construction!
:::

## SAW Terminology

:::{warning}
This section is under construction!
:::

## Running Example

:::{warning}
This section is under construction!
:::
