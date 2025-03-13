# Invoking SAW

:::{warning}
This section is under construction!
:::

There are three ways to run `saw`.
The most common is to provide the name of a SAWScript file to run:
`saw proofs.saw`.
If you leave the file name off, or give the `-I` option, SAW will
start an interactive read-eval-print loop ("REPL").
It is also possible to use the `-B` ("batch") option to pass a file of
REPL commands to run.
This allows automated use of the REPL's `:`-commands.

See [the REPL reference](./appendices/repl-reference) for additional details about
the `saw` executable and its options.
