# External SAT Solvers

In addition to the `abc`, `z3`, and `yices` proof tactics used
above, SAWScript can also invoke arbitrary external SAT solvers
that read CNF files and produce results according to the SAT
competition
[input and output conventions](https://jix.github.io/varisat/manual/0.2.0/formats/dimacs.html),
using the `external_cnf_solver` tactic. For example, you can use
[PicoSAT](http://fmv.jku.at/picosat/) to prove the theorem `thm` from
the last example, with the following commands:

:::{code-block} sawscript
let picosat = external_cnf_solver "picosat" ["%f"];
prove_print picosat thm;x
:::

The use of `let` is simply a convenient abbreviation. The following
would be equivalent:

:::{code-block} sawscript
prove_print (external_cnf_solver "picosat" ["%f"]) thm;
:::

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
