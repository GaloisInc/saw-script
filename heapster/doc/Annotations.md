# LLVM Heapster Annotations

To support type-preserving compilation, the user (or, more likely, a compiler)
can embed block entry hints _in_ the LLVM IR.

This feature is *highly* experimental.

This works by using a "dummy" function:

```
define void @heapster.require(...) { ret void }
```

To assign a hint to a basic block `B`, insert a call to this 
function in `B`. The arguments are:

- A ghost context to use, binding names to types
- A value permission context, binding:
  1. any ghost name in the context to a permission, 
  2. any toplevel name (ranging over the names `top0 ... topN`) to a permission,
  3. any LLVM instruction dominating the basic block to a permission. In the spec, 
     the names `arg0 ... argN` can be used for these, and then ...
- ... the remaining arguments should be the instructions to _use_ for each `argi`.
  
For example in [](../examples/bc-annot/foo.ll) the arguments to
`@heapster.require` in the last basic block of `@foo` are:

- the string `@.ghosts` contains a ghost context string
- the string `@.spec` contains a spec assigning permissions not only to the ghosts and toplevels, but also `arg0` and `arg1`.
- the argument `%1`, meaning use `%1` for `arg0`
- the argument `%0`, meaning use `%0` for `arg1`
