# The Languages in SAW

One of the things that can be confusing about SAW is that there is a
multiplicity of languages involved.

The most important languages in SAW are:
 - Cryptol, which is a modeling and specification language;
 - SAWScript, which is an application-level scripting and control language;
 - Python, which can be used as an alternative to SAWScript;
 - SAWCore, which is a dependently-typed proof language and a common
   interchange substrate.

Some degree of familiarity with Cryptol is needed for nearly all SAW
tasks.
SAWScript is also necessary unless exclusively using the Python interface;
even then, some familiarity with SAWScript is helpful for reading examples
and documentation.

Conversely, however, users of SAW do not need to learn SAWCore.
For some advanced topics it will become necessary (or at least very
helpful) to be able to look at a SAWCore term and guess more or less
what it means.
In general only SAW developers need to be able to _write_ SAWCore, and
then only rarely.

SAW can also load code for verification in these other languages:
 - LLVM bitcode
 - JVM byte code
 - the Rust "MIR" intermediate language
 - raw x86_64 machine code

and these languages' types and concepts also appear from time to time.
We therefore recommend picking up at least a basic familiarity with
the types and concepts of the backend or backends you are using; for
example, when verifying C code, it is helpful to understand how LLVM
thinks about bitvectors and records and how Clang translates C types
to LLVM types.

The following additional languages can also be involved:
 - SMT-LIB, which is a common logic shared among SMT solvers;
 - What4, which is a slightly higher-level wrapper around SMT-LIB;
 - Gallina, the Rocq theorem proving environment's specification
   language.


SMT-LIB is normally only of interest to SAW developers, when debugging the
SMT queries it sends to solvers.
However, a conceptual-level understanding of SMT-LIB and what SMT
solvers can and cannot do is helpful for understanding SAW.
Because SAW is intended to mostly do automated proofs, many of the
restrictions of solvers manifest as restrictions or limitations in SAW
as well.
What4 should be invisible to users; it appears in this list for
completeness.

Gallina and Rocq become involved because SAW can export to Rocq for
proving.

A typical proof development using SAW will contain, besides the code
being verified, a collection of models or abstract specifications
written in Cryptol, a collection of precondition/postcondition
specifications written in SAWScript, and also a collection of
SAWScript code that runs the proofs of the specifications against the
code.


