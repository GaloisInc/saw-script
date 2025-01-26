# Introduction

SAWScript is a special-purpose programming language developed by
Galois to help orchestrate and track the results of the large
collection of proof tools necessary for analysis and verification of
complex software artifacts.

The language adopts the functional paradigm, and largely follows the
structure of many other typed functional languages, with some special
features specifically targeted at the coordination of verification and
analysis tasks.

This tutorial introduces the details of the language by walking through
several examples, and showing how simple verification tasks can be
described. The complete examples are available [on
GitHub](https://github.com/GaloisInc/saw-script/tree/master/doc/tutorial/code).
Most of the examples make use of inline specifications written in
Cryptol, a language originally designed for high-level descriptions of
cryptographic algorithms. For readers unfamiliar with Cryptol, various
documents describing its use are available
[here](http://cryptol.net/documentation.html).
