# Example: Find First Set

As a first example, we consider showing the equivalence of several quite
different implementations of the POSIX `ffs` function, which identifies
the position of the first ``1`` bit in a word. The function takes an
integer as input, treated as a vector of bits, and returns another
integer which indicates the index of the first bit set (zero being the
least significant). This function can be implemented in several ways
with different performance and code clarity tradeoffs, and we would like
to show those different implementations are equivalent.

## Reference Implementation

One simple implementation takes the form of a loop with an index
initialized to zero, and a mask initialized to have the least
significant bit set. On each iteration, we increment the index, and
shift the mask to the left. Then we can use a bitwise "and" operation to
test the bit at the index indicated by the index variable. The following
C code (which is also in the `ffs.c` file on GitHub) uses this approach.

:::{literalinclude} code/ffs.c
:lines: 9-17
:language: c
:::

This implementation is relatively straightforward, and a proficient C
programmer would probably have little difficulty believing its
correctness. However, the number of branches taken during execution
could be as many as 32, depending on the input value. It's possible to
implement the same algorithm with significantly fewer branches, and no
backward branches.

## Alternative Implementations

An alternative implementation, taken by the following function (also in
`ffs.c`), treats the bits of the input word in chunks, allowing
sequences of zero bits to be skipped over more quickly.

:::{literalinclude} code/ffs.c
:lines: 19-26
:language: c
:::

Another optimized version, in the following rather mysterious program
(also in `ffs.c`), based on the `ffs` implementation in [musl
libc](http://musl.libc.org/).

:::{literalinclude} code/ffs.c
:lines: 69-76
:language: c
:::

These optimized versions are much less obvious than the reference
implementation. They might be faster, but how do we gain confidence
that they calculate the same results as the reference implementation?

Finally, consider a buggy implementation which is correct on all but one
possible input (also in `ffs.c`). Although contrived, this program
represents a case where traditional testing -- as opposed to
verification -- is unlikely to be helpful.

:::{literalinclude} code/ffs.c
:lines: 43-47
:language: c
:::

SAWScript allows us to state these problems concisely, and to quickly
and automatically 1) prove the equivalence of the reference and
optimized implementations on all possible inputs, and 2) find an input
exhibiting the bug in the third version.

## Generating LLVM Code

SAW can analyze LLVM code, but most programs are originally written in a
higher-level language such as C, as in our example. Therefore, the C
code must be translated to LLVM, using something like the following
command:

:::{code-block} console
$ clang -g -c -emit-llvm -o ffs.bc ffs.c
:::

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

:::{code-block} console
$ make ffs.bc
:::

## Equivalence Proof

We now show how to use SAWScript to prove the equivalence of the
reference and implementation versions of the FFS algorithm, and
exhibit the bug in the buggy implementation.

A SAWScript program is typically structured as a sequence of commands,
potentially along with definitions of functions that abstract over
commonly-used combinations of commands.

The following script (in `ffs_llvm.saw`) is sufficient to automatically
prove the equivalence of `ffs_ref` with `ffs_imp` and `ffs_musl`, and
identify the bug in `ffs_bug`.

:::{literalinclude} code/ffs_llvm.saw
:language: sawscript
:::

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

:::{code-block} console
$ saw ffs_llvm.saw



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
:::

Note that both explicitly searching for an input exhibiting the bug
(with `sat`) and attempting to prove the false equivalence (with
`prove`) exhibit the bug. Symmetrically, we could use `sat` to prove the
equivalence of `ffs_ref` and `ffs_imp`, by checking that the
corresponding disequality is unsatisfiable. Indeed, this exactly what
happens behind the scenes: `prove abc <goal>` is essentially `not (sat
abc (not <goal>))`.

## Cross-Language Proofs

We can implement the FFS algorithm in Java with code almost identical
to the C version.

The reference version (in `FFS.java`) uses a loop, like the C version:

:::{literalinclude} code/FFS.java
:lines: 2-10
:language: java
:::

And the efficient implementation uses a fixed sequence of masking and
shifting operations:

:::{literalinclude} code/FFS.java
:lines: 12-19
:language: java
:::

Although in this case we can look at the C and Java code and see that
they perform almost identical operations, the low-level operators
available in C and Java do differ somewhat. Therefore, it would be
nice to be able to gain confidence that they do, indeed, perform the
same operation.

We can do this with a process very similar to that used to compare the
reference and implementation versions of the algorithm in a single
language.

First, we compile the Java code to a JVM class file.

:::{code-block} console
$ javac -g FFS.java
:::

Like with `clang`, the `-g` flag instructs `javac` to include debugging
information, which can be useful to preserve variable names.

Using `saw` with Java code requires a command-line option `-b` that
locates Java. Run the code in this section with the command:

:::{code-block} console
$ saw -b <path to directory where Java lives> ffs_compare.saw
:::

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

:::{literalinclude} code/ffs_compare.saw
:language: sawscript
:::

Here, the `jvm_extract` function works like `llvm_extract`, but on a
Java class and method name. The `prove_print` command works similarly
to the `prove` followed by `print` combination used for the LLVM
example above.
