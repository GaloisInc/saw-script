# Using SMT-Lib Solvers

The examples presented so far have used the internal proof system
provided by SAWScript, based primarily on a version of the ABC tool
from UC Berkeley linked into the `saw` executable. However, there is
internal support for other proof tools -- such as Yices and Z3 as
illustrated in the next example -- and more general support for
exporting models representing theorems as goals in the SMT-Lib
language. These exported goals can then be solved using an external
SMT solver.

Consider the following C file:

:::{literalinclude} code/double.c
:language: c
:::

In this trivial example, an integer can be doubled either using
multiplication or shifting. The following SAWScript program (in
`double.saw`) verifies that the two are equivalent using both internal
Yices and Z3 modes, and by exporting an SMT-Lib theorem to be
checked later, by an external SAT solver.

:::{literalinclude} code/double.saw
:language: sawscript
:::

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

The SMT-Lib export capabilities in SAWScript make use of the Haskell SBV
package, and support ABC, Bitwuzla, Boolector, CVC4, CVC5, MathSAT, Yices, and
Z3.
