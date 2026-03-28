(repl-reference)=
# SAW REPL Reference

The primary mechanism for interacting with SAW is through the `saw`
executable included as part of the standard binary distribution. With no
arguments, `saw` starts a read-evaluate-print loop (REPL) that allows
the user to interactively evaluate commands in the SAWScript language.

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
