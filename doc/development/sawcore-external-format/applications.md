# Applications

Computations in SAWCore are accomplished by applying operators (or any
term of function type) to operands. Application is structured in
"curried" form: each application node applies a node of function type
to one argument. Functions that take multiple arguments require
multiple application nodes. For example, to add two 8-bit bit vectors,
we can use the following code:

:::{code-block} text
1 Global Prelude.bitvector
2 Nat 8
3 App 1 2
4 ExtCns 0 "x" 3
5 ExtCns 1 "y" 3
6 Global Prelude.bvAdd
7 App 6 2
8 App 7 4
9 App 8 5
:::

This snippet applies the builtin `bitvector` type to the natural
number 8, to form the type of the input variables. These inputs are
then declared on lines 4 and 5. Line 7 then applies the builtin
`bvAdd` to the natural number 8 (to tell it the size of the following
bit vectors). Finally, lines 8 and 9 continue the application to
include the two input variables.
