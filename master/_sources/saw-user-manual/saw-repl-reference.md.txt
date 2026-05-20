(repl-reference)=
# SAW REPL Reference

The primary mechanism for interacting with SAW is through the `saw`
executable included as part of the standard binary distribution. With no
arguments, `saw` starts a read-evaluate-print loop (REPL) that allows
the user to interactively evaluate commands in the SAWScript language.

## REPL Commands

There are a number of REPL-specific commands that can be accessed by
typing a colon and the command name, and perhaps some arguments.

- `:?` prints the list of `:`-commands with brief descriptions.
  If given an argument, it instead looks up a SAWScript builtin and
  prints its type and help text.

- `:cd` changes the REPL's current directory.

- `:env` displays the values and types of all currently bound
  variables, including built-in functions and commands.

- `:help` or `:h` is the same as `:?`.

- `:llvmdis` disassembles an LLVM module.
  See separate subsection below.

- `:pwd` prints the REPL's current directory.

- `:quit` or `:q` exits the REPL.
  (If the REPL was started as a subshell, it only exits that subshell,
  not the whole of SAW.)

- `:search` with one or more types (complex types go in parentheses)
  prints matching currently bound variables.
  See separate subsection below.

- `:tenv` displays the values and types of all currently bound types
  and type aliases, including many (but currently not all) built-in
  types.

- `:type` or `:t` checks and prints the type of an arbitrary SAWScript
  expression:

  :::{code-block} console
  sawscript> :t show
  {a.0} a.0 -> String
  :::

### Using `:search`

The REPL `:search` command takes one or more type patterns as arguments,
and searches the current value namespace (including functions and builtins)
for objects that mention types matching all the patterns given.
In practice this is mostly useful for searching for builtins.

Type patterns are type names extended with `_` as a wildcard.
Thus for example `[_]` matches any list type.
You may also forall-bind type variables before the patterns using the
`{a}` syntax.
The scope of such bindings is the whole search.

Complex patterns should be written in parentheses; otherwise they
become syntactically ambiguous.
Note in particular that parentheses are required to treat a type constructor
application to another type as a single search term.
Without parentheses, `:search` would treat the unapplied type constructor and
the other type as two separate search terms.
For instance, `:search ProofScript Int` will search for objects mentioning both
`ProofScript` (applied to anything) and `Int`. To search for objects that
mention the type `ProofScript Int`, write `:search (ProofScript Int)`.

Type variables in the search patterns are matched as follows:

- Already-bound type variables (typedef names, certain builtin types)
  must match exactly.

- Free type variables match any type, but all occurrences must match the
  same type.
  Thus for example `[a] -> a` matches `sum : [Int] -> Int` and
  `head : {t} [t] -> t` but not `length : {t} [t] -> Int`.

  This is true across all patterns in the same search; searching for
  `[a]`, `[b]`, and `a -> b` will match
  `map : {a, b} (a -> b) -> [a] -> [b]`, as well as
  `pam : {a, b} [a] -> (a -> b) -> [b]` if you define such a thing.
  But it won't match
  `mapFirst : {a, b, c} (a -> b) [(a, c)] -> [(b, c)]`.

  Perhaps unfortunately, it _will_ match
  `intNth : [Int] -> Int -> Int`.
  The search logic does not require distinct patterns to match distinct
  parts of the target type, nor is there a way to prevent it from picking
  the same substitution for both `a` and `b`.
  (Neither of these behaviors is entirely desirable and might be improved
  in the future.)

- Forall-bound type variables in the pattern are matched in the same
  way as free type variables, but will _only_ match forall-bound type
  variables in the search space.
  Thus, `:search {a} (a -> a)` will match `id : {a} a -> a` but not
  `inc: Int -> Int`, while `:search (a -> a)` will match both.
  This is helpful to search specifically for polymorphic functions.

Because SAWScript functions are curried, searching for `Int -> Int`
will match `String -> Int -> Int`.
However, it will not match `Int -> String -> Int`.
The best way to search for a function that takes `Int` in _any_
argument position and also returns `Int` is by searching for
both `Int -> _` and `_ -> Int`: `:search (Int -> _) (_ -> Int)`.

There is, however, no good way yet to search for a function that takes
two `Int`s in arbitrary argument positions.
Searching for `Int -> Int -> _` will only find functions where the
two arguments are adjacent, `Int -> _ -> Int -> _` will only find
functions where one other argument is between them, and searching
for `Int -> _` twice falls afoul of the limitation where two
patterns can match the same thing.

### Using `:llvmdis`

`:llvmdis` disassembles LLVM bitcode or prints other metadata from an
`LLVMModule`.
The first argument is the name of a SAWScript-level `LLVMModule` that
has been loaded.

The second argument selects an object to disassemble.
If it is a `!` followed by a number _N_, the _N_th unnamed metadata reference
is extracted and printed.
If it contains a `:`, it is treated as a filename and line number and the
code or data structure associated with that location is extracted and printed.
Otherwise it is treated as a function name to disassemble.

The output is comparable to LLVM's `llvm-dis` tool but is based on
SAW's internal representation and knowledge of the LLVM module.

Examples:

:::{code-block} console
sawscript> bc <- llvm_load_module "intTests/testmulti/foo.bc"
sawscript> :llvmdis bc foo.c:2
  ... shows just line 2 of foo.c in LLVM textual format
sawscript> :llvmdis bc !10
  ... shows the metadata at index 10
sawscript> :llvmdis bc foo
  ... shows the foo function in LLVM textual format
:::
