Introduction
============

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

Example: Find First Set
=======================

As a first example, we consider showing the equivalence of several quite
different implementations of the POSIX `ffs` function, which identifies
the position of the first ``1`` bit in a word. The function takes an
integer as input, treated as a vector of bits, and returns another
integer which indicates the index of the first bit set (zero being the
least significant). This function can be implemented in several ways
with different performance and code clarity tradeoffs, and we would like
to show those different implementations are equivalent.

Reference Implementation
-------------------------

One simple implementation takes the form of a loop with an index
initialized to zero, and a mask initialized to have the least
significant bit set. On each iteration, we increment the index, and
shift the mask to the left. Then we can use a bitwise "and" operation to
test the bit at the index indicated by the index variable. The following
C code (which is also in the `ffs.c` file on GitHub) uses this approach.

``` {.c}
$include 9-17 code/ffs.c
```

This implementation is relatively straightforward, and a proficient C
programmer would probably have little difficulty believing its
correctness. However, the number of branches taken during execution
could be as many as 32, depending on the input value. It's possible to
implement the same algorithm with significantly fewer branches, and no
backward branches.

Alternative Implementations
---------------------------

An alternative implementation, taken by the following function (also in
`ffs.c`), treats the bits of the input word in chunks, allowing
sequences of zero bits to be skipped over more quickly.

``` {.c}
$include 19-26 code/ffs.c
```

Another optimized version, in the following rather mysterious program
(also in `ffs.c`), based on the `ffs` implementation in [musl
libc](http://www.musl-libc.org/).

``` {.c}
$include 69-76 code/ffs.c
```

These optimized versions are much less obvious than the reference
implementation. They might be faster, but how do we gain confidence
that they calculate the same results as the reference implementation?

Finally, consider a buggy implementation which is correct on all but one
possible input (also in `ffs.c`). Although contrived, this program
represents a case where traditional testing -- as opposed to
verification -- is unlikely to be helpful.

``` {.c}
$include 43-47 code/ffs.c
```

SAWScript allows us to state these problems concisely, and to quickly
and automatically 1) prove the equivalence of the reference and
optimized implementations on all possible inputs, and 2) find an input
exhibiting the bug in the third version.

Generating LLVM Code
--------------------

SAW can analyze LLVM code, but most programs are originally written in a
higher-level language such as C, as in our example. Therefore, the C
code must be translated to LLVM, using something like the following
command:

    > clang -g -c -emit-llvm -o ffs.bc ffs.c

The `-g` flag instructs `clang` to include debugging information, which
is useful in SAW to refer to variables and struct fields using the same
names as in C. We have tested SAW successfully with versions of `clang`
from 3.6 to 7.0. Please report it as a bug [on
GitHub](https://github.com/GaloisInc/saw-script/issues) if SAW fails to
parse any LLVM bitcode file.

This command, and following command examples in this tutorial, can be
run from the `code` directory [on
GitHub](https://github.com/GaloisInc/saw-script/tree/master/doc/tutorial/code).
A `Makefile` also exists in that directory, providing quick shortcuts
for tasks like this. For instance, we can get the same effect as the
previous command by running:

    > make ffs.bc

\newpage

Equivalence Proof
-----------------

We now show how to use SAWScript to prove the equivalence of the
reference and implementation versions of the FFS algorithm, and
exhibit the bug in the buggy implementation.

A SAWScript program is typically structured as a sequence of commands,
potentially along with definitions of functions that abstract over
commonly-used combinations of commands.

The following script (in `ffs_llvm.saw`) is sufficient to automatically
prove the equivalence of `ffs_ref` with `ffs_imp` and `ffs_musl`, and
identify the bug in `ffs_bug`.

```
$include all code/ffs_llvm.saw
```

In this script, the `print` commands simply display text for the user.
The `llvm_extract` command instructs the SAWScript interpreter
to perform symbolic simulation of the given C function (e.g., `ffs_ref`)
from a given bitcode file (e.g., `ffs.bc`), and return a term
representing the semantics of the function.

The `let` statement then constructs a new term corresponding to the
assertion of equality between two existing terms.  Arbitrary
Cryptol expressions can be embedded within SAWScript; to distinguish
Cryptol code from SAWScript commands, the Cryptol code is placed
within double brackets `{{` and `}}`.

The `prove` command can verify the validity of such an assertion, or
produce a counter-example that invalidates it. The `abc` parameter
indicates what theorem prover to use; SAWScript offers support for many
other SAT and SMT solvers as well as user definable simplification
tactics.

Similarly, the `sat` command works in the opposite direction to `prove`.
It attempts to find a value for which the given assertion is true, and
fails if there is no such value.

If the `saw` executable is in your PATH, you can run the script above with

    > saw ffs_llvm.saw

producing the output

```
Loading file "ffs_llvm.saw"
Extracting reference term: ffs_ref
Extracting implementation term: ffs_imp
Extracting implementation term: ffs_musl
Extracting buggy term: ffs_bug
Proving equivalence: ffs_ref == ffs_imp
Valid
Proving equivalence: ffs_ref == ffs_musl
Valid
Finding bug via sat search: ffs_ref != ffs_bug
Sat: [x = 0x101010]
Finding bug via failed proof: ffs_ref == ffs_bug
prove: 1 unsolved subgoal(s)
Invalid: [x = 0x101010]
Done.
```

Note that both explicitly searching for an input exhibiting the bug
(with `sat`) and attempting to prove the false equivalence (with
`prove`) exhibit the bug. Symmetrically, we could use `sat` to prove the
equivalence of `ffs_ref` and `ffs_imp`, by checking that the
corresponding disequality is unsatisfiable. Indeed, this exactly what
happens behind the scenes: `prove abc <goal>` is essentially `not (sat
abc (not <goal>))`.

Cross-Language Proofs
---------------------

We can implement the FFS algorithm in Java with code almost identical
to the C version.

The reference version (in `FFS.java`) uses a loop, like the C version:

``` {.java}
$include 2-10 code/FFS.java
```

And the efficient implementation uses a fixed sequence of masking and
shifting operations:

``` {.java}
$include 12-19 code/FFS.java
```

Although in this case we can look at the C and Java code and see that
they perform almost identical operations, the low-level operators
available in C and Java do differ somewhat. Therefore, it would be
nice to be able to gain confidence that they do, indeed, perform the
same operation.

We can do this with a process very similar to that used to compare the
reference and implementation versions of the algorithm in a single
language.

First, we compile the Java code to a JVM class file.

    > javac -g FFS.java

Like with `clang`, the `-g` flag instructs `javac` to include debugging
information, which can be useful to preserve variable names.

Using `saw` with Java code requires a command-line option `-b` that
locates Java. Run the code in this section with the command:

    > saw -b <path to directory where Java lives> ffs_compare.saw

Alternatively, if Java is located on your `PATH`, you can omit the `-b`
option entirely.

Both Oracle JDK and OpenJDK versions 6 through 8 work well with SAW.
SAW also includes experimental support for JDK 9 and later. Code that only
involves primitive data types (such as `FFS.java` above) is known to work well
under JDK 9+, but there are some as-of-yet unresolved issues in verifying code
involving classes such as `String`. For more information on these issues, refer
to [this GitHub issue](https://github.com/GaloisInc/crucible/issues/641).

Now we can do the proof both within and across languages (from
`ffs_compare.saw`):

```
$include all code/ffs_compare.saw
```

Here, the `jvm_extract` function works like `llvm_extract`, but on a
Java class and method name. The `prove_print` command works similarly
to the `prove` followed by `print` combination used for the LLVM
example above.

Using SMT-Lib Solvers
=====================

The examples presented so far have used the internal proof system
provided by SAWScript, based primarily on a version of the ABC tool
from UC Berkeley linked into the `saw` executable. However, there is
internal support for other proof tools -- such as Yices and Z3 as
illustrated in the next example -- and more general support for
exporting models representing theorems as goals in the SMT-Lib
language. These exported goals can then be solved using an external
SMT solver.

Consider the following C file:

``` {.c}
$include all code/double.c
```

In this trivial example, an integer can be doubled either using
multiplication or shifting. The following SAWScript program (in
`double.saw`) verifies that the two are equivalent using both internal
ABC, Yices, and Z3 modes, and by exporting an SMT-Lib theorem to be
checked later, by an external SAT solver.

```
$include all code/double.saw
```

The new primitives introduced here are the tilde operator, `~`, which
constructs the logical negation of a term, and `write_smtlib2`, which
writes a term as a proof obligation in SMT-Lib version 2 format. Because
SMT solvers are satisfiability solvers, their default behavior is to
treat free variables as existentially quantified. By negating the input
term, we can instead treat the free variables as universally quantified:
a result of "unsatisfiable" from the solver indicates that the original
term (before negation) is a valid theorem. The `prove` primitive does
this automatically, but for flexibility the `write_smtlib2` primitive
passes the given term through unchanged, because it might be used for
either satisfiability or validity checking.

The SMT-Lib export capabilities in SAWScript make use of the Haskell
SBV package, and support ABC, Boolector, CVC4, MathSAT, Yices, and Z3.

\newpage

External SAT Solvers
====================

In addition to the `abc`, `z3`, and `yices` proof tactics used
above, SAWScript can also invoke arbitrary external SAT solvers
that read CNF files and produce results according to the SAT
competition
[input and output conventions](http://www.satcompetition.org/2009/format-solvers2009.html),
using the `external_cnf_solver` tactic. For example, you can use
[PicoSAT](http://fmv.jku.at/picosat/) to prove the theorem `thm` from
the last example, with the following commands:

    let picosat = external_cnf_solver "picosat" ["%f"];
    prove_print picosat thm;

The use of `let` is simply a convenient abbreviation. The following
would be equivalent:

    prove_print (external_cnf_solver "picosat" ["%f"]) thm;

The first argument to `external_cnf_solver` is the name of the
executable. It can be a fully-qualified name, or simply the bare
executable name if it's in your PATH. The second argument is an array
of command-line arguments to the solver. Any occurrence of `%f` is
replaced with the name of the temporary file containing the CNF
representation of the term you're proving.

The `external_cnf_solver` tactic is based on the same underlying
infrastructure as the `abc` tactic, and is generally capable of
proving the same variety of theorems.

To write a CNF file without immediately invoking a solver, use the
`offline_cnf` tactic, or the `write_cnf` top-level command.

Compositional Proofs
====================

The examples shown so far treat programs as monolithic entities. A
Java method or C function, along with all of its callees, is
translated into a single mathematical model. SAWScript also has
support for more compositional proofs, as well as proofs about
functions that use heap data structures.

Compositional Imperative Proofs
-------------------------------

As a simple example of compositional reasoning on imperative programs,
consider the following Java code.

``` {.java}
$include all code/Add.java
```

Here, the `add` function computes the sum of its arguments. The `dbl`
function then calls `add` to double its argument. While it would be easy
to prove that `dbl` doubles its argument by following the call to `add`,
it's also possible in SAWScript to prove something about `add` first,
and then use the results of that proof in the proof of `dbl`, as in the
following SAWScript code (`java_add.saw` on GitHub).

\newpage

````
$include all code/java_add.saw
````

This can be run as follows:

    > saw -b <path to directory where Java lives> java_add.saw

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

Interactive Interpreter
=======================

The examples so far have used SAWScript in batch mode on complete
script files. It also has an interactive Read-Eval-Print Loop (REPL)
which can be convenient for experimentation. To start the REPL, run
SAWScript with no arguments:

    > saw

The REPL can evaluate any command that would appear at the top level
of a standalone script, or in the `main` function, as well as a few
special commands that start with a colon:

\newpage

    :env     display the current sawscript environment
    :type    check the type of an expression
    :browse  display the current environment
    :eval    evaluate an expression and print the result
    :?       display a brief description about a built-in operator
    :help    display a brief description about a built-in operator
    :quit    exit the REPL
    :load    load a module
    :add     load an additional module
    :cd      set the current working directory

As an example of the sort of interactive use that the REPL allows,
consider the file `code/NQueens.cry`, which provides a Cryptol
specification of the problem of placing a specific number of queens on
a chess board in such a way that none of them threaten any of the
others.

````
$include 21-56 code/NQueens.cry
````

This example gives us the opportunity to use the satisfiability
checking capabilities of SAWScript on a problem other than
equivalence verification.

First, we can load a model of the `nQueens` term from the Cryptol file.

    sawscript> m <- cryptol_load "NQueens.cry"
    sawscript> let nq8 = {{ m::nQueens`{8} }}

Once we've extracted this model, we can try it on a specific
configuration to see if it satisfies the property that none of the
queens threaten any of the others.

    sawscript> print {{ nq8 [0,1,2,3,4,5,6,7] }}
    False

This particular configuration didn't work, but we can use the
satisfiability checking tools to automatically find one that does.

    sawscript> sat_print abc nq8
    Sat [qs = [3, 1, 6, 2, 5, 7, 4, 0]]

And, finally, we can double-check that this is indeed a valid solution.

    sawscript> print {{ nq8 [3,1,6,2,5,7,4,0] }}
    True

Other Examples
==============

The `code` directory [on
GitHub](https://github.com/GaloisInc/saw-script/tree/master/doc/tutorial/code)
contains a few additional examples not mentioned so far. These remaining
examples don't cover significant new material, but help fill in some
extra use cases that are similar, but not identical to those already
covered.

Java Equivalence Checking
-------------------------

The previous examples showed comparison between two different LLVM
implementations, and cross-language comparisons between Cryptol, Java,
and LLVM. The script in `ffs_java.saw` compares two different Java
implementations, instead.

````
$include all code/ffs_java.saw
````

As with previous Java examples, this one needs to be run with the `-b`
flag to tell the interpreter where to find Java:

    > saw -b <path to directory where Java lives> ffs_java.saw

AIG Export and Import
---------------------

Most of the previous examples have used the `abc` tactic to discharge
theorems. This tactic works by translating the given term to
And-Inverter Graph (AIG) format, transforming the graph in various
ways, and then using a SAT solver to complete the proof.

Alternatively, the `write_aig` command can be used to write an AIG
directly to a file, in [AIGER format](http://fmv.jku.at/aiger/), for
later processing by external tools, as shown in
`code/ffs_gen_aig.saw`.

````
$include all code/ffs_gen_aig.saw
````

Conversely, the `read_aig` command can construct an internal term from
an existing AIG file, as shown in `ffs_compare_aig.saw`.

````
$include all code/ffs_compare_aig.saw
````

We can use external AIGs to verify the equivalence as follows,
generating the AIGs with the first script and comparing them with the
second:

    > saw -b <path to directory where Java lives> ffs_gen_aig.saw
    > saw ffs_compare_aig.saw

Files in AIGER format can be produced and processed by several
external tools, including ABC, Cryptol version 1, and various hardware
synthesis and verification systems.
