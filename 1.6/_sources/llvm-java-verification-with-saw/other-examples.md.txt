# Other Examples

The `code` directory [on
GitHub](https://github.com/GaloisInc/saw-script/tree/master/doc/tutorial/code)
contains a few additional examples not mentioned so far. These remaining
examples don't cover significant new material, but help fill in some
extra use cases that are similar, but not identical to those already
covered.

## Java Equivalence Checking

The previous examples showed comparison between two different LLVM
implementations, and cross-language comparisons between Cryptol, Java,
and LLVM. The script in `ffs_java.saw` compares two different Java
implementations, instead.

:::{literalinclude} code/ffs_java.saw
:language: sawscript
:::

As with previous Java examples, this one needs to be run with the `-b`
flag to tell the interpreter where to find Java:

:::{code-block} console
$ saw -b <path to directory where Java lives> ffs_java.saw
:::

## AIG Export and Import

Most of the previous examples have used the `abc` tactic to discharge
theorems. This tactic works by translating the given term to
And-Inverter Graph (AIG) format, transforming the graph in various
ways, and then using a SAT solver to complete the proof.

Alternatively, the `write_aig` command can be used to write an AIG
directly to a file, in [AIGER format](http://fmv.jku.at/aiger/), for
later processing by external tools, as shown in
`code/ffs_gen_aig.saw`.

:::{literalinclude} code/ffs_gen_aig.saw
:language: sawscript
:::

Conversely, the `read_aig` command can construct an internal term from
an existing AIG file, as shown in `ffs_compare_aig.saw`.

:::{literalinclude} code/ffs_compare_aig.saw
:language: sawscript
:::

We can use external AIGs to verify the equivalence as follows,
generating the AIGs with the first script and comparing them with the
second:

:::{code-block} console
$ saw -b <path to directory where Java lives> ffs_gen_aig.saw
$ saw ffs_compare_aig.saw
:::

Files in AIGER format can be produced and processed by several
external tools, including ABC, Cryptol version 1, and various hardware
synthesis and verification systems.
