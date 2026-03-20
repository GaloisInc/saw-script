# Introduction

SAW, the Software Analysis Workbench, is a tool for working with
formal models of the computational behavior of software.
It supports numerous input languages and formats and can establish
proofs about many kinds of properties and relationships.
It also has some ability to transform these inputs into other forms
and output them.

If you have C or C++ source code, you can run it through the Clang
compiler and load the resulting LLVM bitcode into SAW.
If you have Rust source, you can run it through a `rustc`/`cargo`
plugin called `mir-json` that dumps out the MIR intermediate
representation in a form that SAW can load.
If you have Java source, you can compile it and load the resulting
Java bytecode into SAW.
There has also been some success verifying code in other languages
whose compilers produce LLVM or Java bytecode.
Beyond this there is also (experimental but rapidly maturing) support
for verifying hardware designs processed by Yosys.

SAW is also designed to work with Cryptol; you can load Cryptol code
or Cryptol models into SAW and prove things about them.
The real strength, however, comes from loading code on the one hand
and a Cryptol model on the other, and proving equivalence.

All of this works because of an underlying proof language known as
SAWCore.
SAWCore serves as a common substrate for importing all these disparate
forms of input and reasoning about them.

SAW falls (mostly) on the solver side of the solver vs. interactive
proving divide.
SAW supports a range of SMT and SAT solvers that can discharge most
proofs.
It also supports two different solver interface libraries: what4 and
SBV, that have somewhat different characteristics.
Proofs that are too large, too complex, or too deep for solvers can be
exported to external proof tools, including the Rocq proof assistant.
(SAW does also have its own experimental interactive proving
interface, but for the time being it is not generally recommended.)

There are some restrictions and limitations, of course.
The biggest limitation is that the symbolic execution SAW uses to
construct models from code needs to be bounded.
This means that the input programs must have fixed-size inputs and
outputs, and all loops (including recursion) must terminate after a
fixed number of iterations.
There are also some unsupported constructs in the LLVM, JVM, and
particularly MIR backends.
See [XXX](XXX) for the full details.


## Notation

:::{warning}
This section is under construction!
:::


## Outline

This manual is divided into two major parts: a user guide, introducing
SAW and the things one can do with SAW; and a reference manual, which
gives a complete breakdown of all the bells and whistles.

The user guide is intended to be read in order, to the extent
feasible; later sections build on earlier sections and we have
attempted to avoid forward references.
The reference manual is intended to be opened to the point that talks
about the thing you need to know about; it makes no attempt to
introduce anything, but also is intended to contain all the details
you might need to know.

A series of appendices provides additional supplementary information.
