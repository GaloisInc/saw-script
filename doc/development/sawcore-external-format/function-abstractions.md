# Function Abstractions

SAWCore allows the creation of function abstractions. The construct
`Lam <type> <body>` causes a function argument value of the given type
to be bound within the term specified by the second argument.
Functions with multiple arguments are constructed with multiple nested
`Lam` nodes. Within the term, an argument can be accessed by the
construct `Var <n> <type>` where an index of `0` corresponds to the
variable bound by the most recent enclosing `Lam`, an index of `1`
corresponds to the variable bound by a `Lam` one level removed, and so
on. Function abstractions can allow code to be abstracted over
different arguments, and applied multiple times in multiple contexts.
They can also be used as an alternative to the `ExtCns` inputs
described previously.

As an example, the code presented earlier in the Application section,
to add two 8-bit bit vector arguments, could be restructured to use
`Lam` and `Var` as follows:

:::{code-block} text
1 Global Prelude.bitvector
2 Nat 8
3 App 1 2
4 Global Prelude.bvAdd
5 App 4 2
6 Var 0 3
7 Var 1 3
8 App 5 6
9 App 8 7
10 Lam x 3 9
11 Lam x 3 10
:::
