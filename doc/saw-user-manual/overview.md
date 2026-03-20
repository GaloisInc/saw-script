# Overview of SAW and SAW's Structure

Now that you've seen SAW and run a couple simple proofs, it's time to
provide some context for going deeper.
Like in any other proof system, a SAW development is structured as a
collection of theorems and proofs.
SAW is a little different, however, because it makes the metalanguage
(called SAWScript) more prominent than usual; in some cases perhaps
too prominent.
This emphasis on scripting proofs has led to SAW having a whole second
front end based on Python.
In the Python interface, Python replaces SAWScript; however, both
manipulate the same internal objects and proof states.

Thus, in the same way that a web browser can be seen as an underlying
system of objects that can be manipulated with JavaScript or with Web
Assembly, SAW can be seen as an underlying system of objects that can
be manipulated with either SAWScript or Python.
This manual, accordingly, concentrates on documenting the underlying
concepts and subsystems with less emphasis on explaining the concrete
syntax.
Examples are given in (to the extent currently practical) both
SAWScript and Python.
The SAWScript language itself is not introduced in detail until
[XXX](XXX); it is sometimes necessary to program in it, but for
routine proofs and developments it is usually sufficient to use the
stylized forms suggested in the next few sections.

## Key Subsystems

The most fundamental component of SAW is a language called SAWCore.
SAWCore is a dependently-typed lambda calculus used as a common
interchange language for higher-level material and for proof
obligations and proof terms.
The underlying SAWCore library provides an internal representation
of SAWCore and an encapsulated interface to the rest of the system
intended to prevent unsound manipulations.

Atop SAWCore is a proof system that keeps track of both proved
theorems and also the goals and hypotheses of any proof in progress.
This is, eventually, intended to provide an encapsulated interface to
the rest of the system intended to prevent unsound manipulations.
The proof system also includes the solver interface; SAWCore is
lowered to SMTlib and sent to any of a range of external solvers
for analysis.

A range of additional functional modules rest on top of the proof
system and SAWCore.
The largest of these is the Crucible interface.
Crucible is a symbolic execution library; it is used to handle
impure/stateful external code that is difficult to represent directly
in SAWCore.
The LLVM, JVM, and MIR (Rust) verification support, as well as
the experimental x86_64 binary verification support, is based on
symbolic execution using Crucible.

Other substantial chunks of functionality include the Cryptol importer
(that translates Cryptol to SAWCore), the Rocq exporter (that translates
SAWCore to Gallina for Rocq) and the Yosys importer (that translates
hardware designs from Yosys's JSON representation to SAWCore).
There is also code for handling and-inverter graphs (AIGs), support
for boolean circuits and formulae in conjunctive normal form (CNF),
and code for exporting to Verilog.
<!-- also bisimulation and automatch... -->

## Typical / Common Use Cases

The most common use case for SAW is importing some code on the one
hand, and a Cryptol model on the other, and proving equivalence
between the two.
As noted, this can be done for C code, Rust code, Java code, and
experimentally for arbitrary x86_64 binaries.
There has also been some success using the LLVM interface for Ada
code; in principle it can be used for any compiler with an LLVM
backend.

Probably the next most common use case is to prove things about
Cryptol models, either properties of a single model or refinement
relationships between increasingly detailed models.
While Cryptol has its own solver interface and many things can be
proven directly from Cryptol, it often proves helpful (or necessary)
to use SAW's more sophisticated proof interface.
(This often does not require resorting to SAW's manual proof
interface; SAW also provides more facilities for working with
solvers.)

One can also import a hardware design and prove it equivalent to a
Cryptol model.
This is still experimental, but maturing rapidly, and modulo some
restrictions on what Yosys features it handles will work for anything
Yosys can import. That includes both Verilog and VHDL.

There is a range of other more exotic functionality available; for
years a wide variety of research ideas were bolted onto SAW because it
was convenient to do so.

Also note that, like Cryptol, SAW was built first to verify
cryptographic code.
It is not intended to be _limited_ to cryptographic code; however, its
assumptions, limitations, design structure, areas of unimplemented
functionality, and so forth reflect this fact.
You are unlikely to run into significant problems with SAW itself when
verifying classical cryptographic code (post-quantum cryptography can
be a bit more difficult); however, the further afield from that core
domain you venture the more likely you are to encounter complications.

## Terminology

<!--

- uninterpret

-->

:::{warning}
This section is under construction!
:::

## Running Example

:::{warning}
This section is under construction!
:::
