
# Heapster Developer Documentation

This directory contains an implementation of the Heapster portion of SAW.

## Overall Code Structure

The central components of Heapster are in the following files:

* Permissions.hs: This file defines the language of _permissions_, which are the types in Heapster. Heapster permissions are defined by the `ValuePerm` datatype, which is defined mutually with the type `PermExpr` of Heapster expressions. See [here](../../../../doc/Permissions.md) for more detail on the Heapster permission langauge.

* Implication.hs: This file defines the concept of _permission implication_ in Heapster, which is a form of subtyping on the Heapster permission types. Permission implication is defined by the `PermImpl` type, which represents a proof that one permission implies, or is a subtype of, another. This file also contains the implication prover, which is the algorithm that attempts to build permission implication proofs. The implication rules are described [here](../../../../doc/Rules.md), while the implication prover is described [here](../../../../doc/ImplProver.md).

* TypedCrucible.hs: This file defines a version of Crucible control-flow graphs (CFGs) that have been type-checked by Heapster. Each Crucible data type used to define CFGs, including the type `CFG` itself, has a corresponding data type in TypedCrucible.hs with `"Typed"` prefixed to its name. This includes the `TypedCFG` type used to represent an entire typed-checked CFG. This file also contains the function `tcCFG` that performs type-checking on a Crucible CFG, along with helper functions used to type-check the various component pieces of Crucible CFGs.

* SAWTranslation.hs: This file defines the translation from type-checked Crucible CFGs to SAW core terms that represent their specifications.

* RustTypes.hs: This file translates Rust types into Heapster types, using a process described [here](../../../../doc/RustTrans.md).

[comment]: <> (FIXME: describe the other files)
