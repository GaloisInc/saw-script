# Compositional Proofs

The examples shown so far treat programs as monolithic entities. A
Java method or C function, along with all of its callees, is
translated into a single mathematical model. SAWScript also has
support for more compositional proofs, as well as proofs about
functions that use heap data structures.

## Compositional Imperative Proofs

As a simple example of compositional reasoning on imperative programs,
consider the following Java code.

:::{literalinclude} code/Add.java
:language: java
:::

Here, the `add` function computes the sum of its arguments. The `dbl`
function then calls `add` to double its argument. While it would be easy
to prove that `dbl` doubles its argument by following the call to `add`,
it's also possible in SAWScript to prove something about `add` first,
and then use the results of that proof in the proof of `dbl`, as in the
following SAWScript code (`java_add.saw` on GitHub).

:::{literalinclude} code/java_add.saw
:language: sawscript
:::

This can be run as follows:

:::{code-block} console
$ saw -b <path to directory where Java lives> java_add.saw
:::

In this example, the definitions of `add_spec` and `dbl_spec` provide
extra information about how to configure the symbolic simulator when
analyzing Java code. In this case, the setup blocks provide explicit
descriptions of the implicit configuration used by
`jvm_extract` (used in the earlier Java FFS example and in the
next section). The `jvm_fresh_var` commands instruct the simulator to
create fresh symbolic inputs to correspond to the Java variables `x` and
`y`. Then, the `jvm_return` commands indicate the expected return value
of the each method, in terms of existing models (which can be written
inline). Because Java methods can operate on references, as well, which
do not exist in Cryptol, Cryptol expressions must be translated to JVM
values with `jvm_term`.

To make use of these setup blocks, the `jvm_verify` command analyzes
the method corresponding to the class and method name provided, using
the setup block passed in as a parameter. It then returns an object
that describes the proof it has just performed. This object can be
passed into later instances of `jvm_verify` to indicate that calls to
the analyzed method do not need to be followed, and the previous proof
about that method can be used instead of re-analyzing it.
