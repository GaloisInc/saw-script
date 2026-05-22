# Interactive Interpreter

The examples so far have used SAWScript in batch mode on complete
script files. It also has an interactive Read-Eval-Print Loop (REPL)
which can be convenient for experimentation. To start the REPL, run
SAWScript with no arguments:

:::{code-block} console
$ saw
:::

The REPL can evaluate any command that would appear at the top level
of a standalone script, or in the `main` function, as well as a few
special commands that start with a colon:

:::{code-block} console

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
:::

As an example of the sort of interactive use that the REPL allows,
consider the file `code/NQueens.cry`, which provides a Cryptol
specification of the problem of placing a specific number of queens on
a chess board in such a way that none of them threaten any of the
others.

:::{literalinclude} code/NQueens.cry
:lines: 21-56
:language: cryptol
:::

This example gives us the opportunity to use the satisfiability
checking capabilities of SAWScript on a problem other than
equivalence verification.

First, we can load a model of the `nQueens` term from the Cryptol file.

:::{code-block} console
sawscript> m <- cryptol_load "NQueens.cry"
sawscript> let nq8 = {{ m::nQueens`{8} }}
:::

Once we've extracted this model, we can try it on a specific
configuration to see if it satisfies the property that none of the
queens threaten any of the others.

:::{code-block} console
sawscript> print {{ nq8 [0,1,2,3,4,5,6,7] }}
False
:::

This particular configuration didn't work, but we can use the
satisfiability checking tools to automatically find one that does.

:::{code-block} console
sawscript> sat_print abc nq8
Sat [qs = [3, 1, 6, 2, 5, 7, 4, 0]]
:::

And, finally, we can double-check that this is indeed a valid solution.

:::{code-block} console
sawscript> print {{ nq8 [3,1,6,2,5,7,4,0] }}
True
:::
