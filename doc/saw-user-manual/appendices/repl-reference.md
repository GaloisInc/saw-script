(repl-reference)=
# REPL Reference

The primary mechanism for interacting with SAW is through the `saw`
executable included as part of the standard binary distribution. With no
arguments, `saw` starts a read-evaluate-print loop (REPL) that allows
the user to interactively evaluate commands in the SAWScript language.
With one file name argument, it executes the specified file as a SAWScript
program.

In addition to a file name, the `saw` executable accepts several
command-line options:

`-h, -?, --help`
: Print a help message.

`-V, --version`
: Show the version of the SAWScript interpreter.

`-c path, --classpath=path`
: Specify a colon-delimited list of paths to search for Java classes.

`-i path, --import-path=path`
: Specify a colon-delimited list of paths to search for imports.

`-t, --extra-type-checking`
: Perform extra type checking of intermediate values.

`-I, --interactive`
: Run interactively (with a REPL). This is the default if no other
  arguments are specified.

`-B file, --batch=file`
: Start the REPL, but load the commands from the given file instead
  of standard input.
  This allows automated use of the REPL `:`-commands and other
  REPL-specific affordances in scripts.

`-j path, --jars=path`
: Specify a colon-delimited list of paths to `.jar` files to search
  for Java classes.

`-b path, --java-bin-dirs`
: Specify a colon-delimited list of paths to search for a Java
  executable.

`-d num, --sim-verbose=num`
: Set the verbosity level of the Java and LLVM simulators.

`-v num, --verbose=num`
: Set the verbosity level of the SAWScript interpreter.

`--clean-mismatched-versions-solver-cache[=path]`
: Run the `clean_mismatched_versions_solver_cache` command on the solver
  cache at the given path, or if no path is given, the solver cache at the
  value of the `SAW_SOLVER_CACHE_PATH` environment variable, then exit. See
  the section **Caching Solver Results** for a description of the
  `clean_mismatched_versions_solver_cache` command and the solver caching
  feature in general.

SAW also uses several environment variables for configuration:

`CRYPTOLPATH`
: Specify a colon-delimited list of directory paths to search for Cryptol
  imports (including the Cryptol prelude).

(path-definition)=
`PATH`
: If the `--java-bin-dirs` option is not set, then the `PATH` will be
  searched to find a Java executable.

`SAW_IMPORT_PATH`
: Specify a colon-delimited list of directory paths to search for imports.

`SAW_JDK_JAR`
: Specify the path of the `.jar` file containing the core Java
  libraries. Note that that is not necessary if the `--java-bin-dirs` option
  or the `PATH` environment variable is used, as SAW can use this information
  to determine the location of the core Java libraries' `.jar` file.

(saw-solver-cache-path-definition)=
`SAW_SOLVER_CACHE_PATH`
: Specify a path at which to keep a cache of solver results obtained during
  calls to certain tactics. A cache is not created at this path until it is
  needed. See the section **Caching Solver Results** for more detail about this
  feature.

On Windows, semicolon-delimited lists are used instead of colon-delimited
lists.

## Using `:search`

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
