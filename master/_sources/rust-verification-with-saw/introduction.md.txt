# Introduction

SAW is a special-purpose programming environment developed by Galois to help
orchestrate and track the results of the large collection of proof tools
necessary for analysis and verification of complex software artifacts.

SAW adopts the functional paradigm, and largely follows the structure of many
other typed functional languages, with some special features specifically
targeted at the coordination of verification and analysis tasks.

This tutorial introduces the details of the language by walking through several
examples, and showing how simple verification tasks can be described. The
complete examples are available [on
GitHub](https://github.com/GaloisInc/saw-script/tree/master/doc/rust-tutorial/code).
Most of the examples make use of inline specifications written in Cryptol, a
language originally designed for high-level descriptions of cryptographic
algorithms. For readers unfamiliar with Cryptol, various documents describing
its use are available [here](http://cryptol.net/documentation.html).

This tutorial also includes a [case study](./case-study-salsa20.md) on how to use
SAW to verify a real-world implementation of the Salsa20 stream cipher based on
the [`stream-ciphers`](https://github.com/RustCrypto/stream-ciphers) Rust
project. The code for this case study is also available [on
GitHub](https://github.com/GaloisInc/saw-script/tree/master/doc/rust-tutorial/code/salsa20).
