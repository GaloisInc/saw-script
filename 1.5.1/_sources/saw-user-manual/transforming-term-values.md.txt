# Transforming Term Values

The three primary functions of SAW are _extracting_ models (`Term`
values) from programs, _transforming_ those models, and _proving_
properties about models using external provers. We've seen how to construct
`Term` values from a range of sources. Now we show how
to use the various term transformation features available in SAW.

## Rewriting

Rewriting a `Term` consists of applying one or more _rewrite rules_ to
it, resulting in a new `Term`. A rewrite rule in SAW can be specified in
multiple ways:

- as the definition of a function that can be unfolded,
- as a term of Boolean type (or a function returning a Boolean) that
  is an equality statement, and
- as a term of _equality type_ with a body that encodes a proof that
  the equality in the type is valid.

In each case the term logically consists of two sides and describes a
way to transform the left side into the right side. Each side may
contain variables (bound by enclosing lambda expressions) and is
therefore a _pattern_ which can match any term in which each variable
represents an arbitrary sub-term. The left-hand pattern describes a term
to match (which may be a sub-term of the full term being rewritten), and
the right-hand pattern describes a term to replace it with. Any variable
in the right-hand pattern must also appear in the left-hand pattern and
will be instantiated with whatever sub-term matched that variable in the
original term.

For example, say we have the following Cryptol function:

:::{code-block} cryptol
 \(x:[8]) -> (x * 2) + 1
:::

We might for some reason want to replace multiplication by a power of
two with a shift. We can describe this replacement using an equality
statement in Cryptol (a rule of form 2 above):

:::{code-block} cryptol
\(y:[8]) -> (y * 2) == (y << 1)
:::

Interpreting this as a rewrite rule, it says that for any 8-bit vector
(call it `y` for now), we can replace `y * 2` with `y << 1`. Using this
rule to rewrite the earlier expression would then yield:

:::{code-block} cryptol
 \(x:[8]) -> (x << 1) + 1
:::

The general philosophy of rewriting is that the left and right patterns,
while syntactically different, should be semantically equivalent.
Therefore, applying a set of rewrite rules should not change the
fundamental meaning of the term being rewritten. SAW is particularly
focused on the task of proving that some logical statement expressed as
a `Term` is always true. If that is in fact the case, then the entire
term can be replaced by the term `True` without changing its meaning. The
rewriting process can in some cases, by repeatedly applying rules that
themselves are known to be valid, reduce a complex term entirely to
`True`, which constitutes a proof of the original statement. In other
cases, rewriting can simplify terms before sending them to external
automated provers that can then finish the job. Sometimes this
simplification can help the automated provers run more quickly, and
sometimes it can help them prove things they would otherwise be unable
to prove by applying reasoning steps (rewrite rules) that are not
available to the automated provers.

In practical use, rewrite rules can be aggregated into `Simpset`
values in SAWScript. A few pre-defined `Simpset` values exist:

- `empty_ss : Simpset` is the empty set of rules. Rewriting with it
should have no effect, but it is useful as an argument to some of the
functions that construct larger `Simpset` values.

- `basic_ss : Simpset` is a collection of rules that are useful in most
proof scripts.

- `cryptol_ss : () -> Simpset` includes a collection of Cryptol-specific
rules. Some of these simplify away the abstractions introduced in the
translation from Cryptol to SAWCore, which can be useful when proving
equivalence between Cryptol and non-Cryptol code. Leaving these
abstractions in place is appropriate when comparing only Cryptol code,
however, so `cryptol_ss` is not included in `basic_ss`.

The following function can apply a `Simpset`:

- `rewrite : Simpset -> Term -> Term` applies a `Simpset` to an existing
`Term` to produce a new `Term`.

To make this more concrete, we examine how the rewriting example
sketched above, to convert multiplication into shift, can work in
practice. We simplify everything with `cryptol_ss` as we go along so
that the `Term`s don't get too cluttered. First, we declare the term
to be transformed:

:::{code-block} console
sawscript> let term = rewrite (cryptol_ss ()) {{ \(x:[8]) -> (x * 2) + 1 }}
sawscript> print_term term
\(x : Prelude.Vec 8 Prelude.Bool) ->
  Prelude.bvAdd 8 (Prelude.bvMul 8 x (Prelude.bvNat 8 2))
    (Prelude.bvNat 8 1)
:::

Next, we declare the rewrite rule:

:::{code-block} console
sawscript> let rule = rewrite (cryptol_ss ()) {{ \(y:[8]) -> (y * 2) == (y << 1) }}
sawscript> print_term rule
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in \(y : x@1) ->
      Cryptol.ecEq x@1 (Cryptol.PCmpWord 8)
        (Prelude.bvMul 8 y (Prelude.bvNat 8 2))
        (Prelude.bvShiftL 8 Prelude.Bool 1 Prelude.False y
           (Prelude.bvNat 1 1))
:::

The primary interface to rewriting uses the `Theorem` type instead of
the `Term` type, as shown in the signatures for `addsimp` and
`addsimps`.

- `addsimp : Theorem -> Simpset -> Simpset` adds a single `Theorem` to a
`Simpset`.

- `addsimps : [Theorem] -> Simpset -> Simpset` adds several `Theorem`
values to a `Simpset`.

A `Theorem` is essentially a `Term` that is proven correct in some way.
In general, a `Theorem` can be any statement, and may not be useful as a
rewrite rule. However, if it has an appropriate shape it can be used for
rewriting. In the ["Proofs about Terms"](proofs-about-terms.md) section,
we'll describe how to construct `Theorem` values from `Term` values.

For the time being, we'll assume we've proved our `rule` term correct in
some way, and have a `Theorem` named `rule_thm`.

Finally, we apply the rule to the target term:

:::{code-block} console
sawscript> let result = rewrite (addsimp rule_thm empty_ss) term
sawscript> print_term result
\(x : Prelude.Vec 8 Prelude.Bool) ->
  Prelude.bvAdd 8
    (Prelude.bvShiftL 8 Prelude.Bool 1 Prelude.False x
       (Prelude.bvNat 1 1))
    (Prelude.bvNat 8 1)
:::

In the absence of user-constructed `Theorem` values, there are some
additional built-in rules that are not included in either `basic_ss` and
`cryptol_ss` because they are not always beneficial, but that can
sometimes be helpful or essential. The `cryptol_ss` simpset includes
rewrite rules to unfold all definitions in the `Cryptol` SAWCore module,
but does not include any of the terms of equality type.

- `add_cryptol_defs : [String] -> Simpset -> Simpset` adds unfolding
rules for functions with the given names from the SAWCore `Cryptol` module
to the given `Simpset`.

- `add_cryptol_eqs : [String] -> Simpset -> Simpset` adds the terms of
equality type with the given names from the SAWCore `Cryptol` module to
the given `Simpset`.

- `add_prelude_defs : [String] -> Simpset -> Simpset` adds unfolding
rules from the SAWCore `Prelude` module to a `Simpset`.

- `add_prelude_eqs : [String] -> Simpset -> Simpset` adds equality-typed
terms from the SAWCore `Prelude` module to a `Simpset`.

Finally, it's possible to construct a theorem from an arbitrary SAWCore
expression (rather than a Cryptol expression), using the `core_axiom`
function.

- `core_axiom : String -> Theorem` creates a `Theorem` from a `String`
in SAWCore syntax. Any `Theorem` introduced by this function is assumed
to be correct, so use it with caution.

## Folding and Unfolding

A SAWCore term can be given a name using the `define` function, and is
then by default printed as that name alone. A named subterm can be
"unfolded" so that the original definition appears again.

- `define : String -> Term -> TopLevel Term`

- `unfold_term : [String] -> Term -> Term`

For example:

:::{code-block} console
sawscript> let t = {{ 0x22 }}
sawscript> print_term t
Cryptol.ecNumber (Cryptol.TCNum 34) (Prelude.Vec 8 Prelude.Bool)
  (Cryptol.PLiteralSeqBool (Cryptol.TCNum 8))
sawscript> t' <- define "t" t
sawscript> print_term t'
t
sawscript> let t'' = unfold_term ["t"] t'
sawscript> print_term t''
Cryptol.ecNumber (Cryptol.TCNum 34) (Prelude.Vec 8 Prelude.Bool)
  (Cryptol.PLiteralSeqBool (Cryptol.TCNum 8))
:::

This process of folding and unfolding is useful both to make large terms
easier for humans to work with and to make automated proofs more
tractable. We'll describe the latter in more detail when we discuss
interacting with external provers.

In some cases, folding happens automatically when constructing Cryptol
expressions. Consider the following example:

:::{code-block} console
sawscript> let t = {{ 0x22 }}
sawscript> print_term t
Cryptol.ecNumber (Cryptol.TCNum 34) (Prelude.Vec 8 Prelude.Bool)
  (Cryptol.PLiteralSeqBool (Cryptol.TCNum 8))
sawscript> let {{ t' = 0x22 }}
sawscript> print_term {{ t' }}
t'
:::

This illustrates that a bare expression in Cryptol braces gets
translated directly to a SAWCore term. However, a Cryptol _definition_
gets translated into a _folded_ SAWCore term. In addition, because the
second definition of `t` occurs at the Cryptol level, rather than the
SAWScript level, it is visible only inside Cryptol braces. Definitions
imported from Cryptol source files are also initially folded and can be
unfolded as needed.

## Other Built-in Transformation and Inspection Functions

In addition to the `Term` transformation functions described so far, a
variety of others also exist.

- `beta_reduce_term : Term -> Term` takes any sub-expression of the form
`(\x -> t) v` in the given `Term` and replaces it with a transformed
version of `t` in which all instances of `x` are replaced by `v`.

- `replace : Term -> Term -> Term -> TopLevel Term` replaces arbitrary
subterms. A call to `replace x y t` replaces any instance of `x` inside
`t` with `y`.

Assessing the size of a term can be particularly useful during benchmarking.
SAWScript provides two mechanisms for this.

- `term_size : Term -> Int` calculates the number of nodes in the
Directed Acyclic Graph (DAG) representation of a `Term` used internally
by SAW. This is the most appropriate way of determining the resource use
of a particular term.

- `term_tree_size : Term -> Int` calculates how large a `Term` would be
if it were represented by a tree instead of a DAG. This can, in general,
be much, much larger than the number returned by `term_size`, and serves
primarily as a way of assessing, for a specific term, how much benefit
there is to the term sharing used by the DAG representation.

Finally, there are a few commands related to the internal SAWCore type of a
`Term`.

- `check_term : Term -> TopLevel ()` checks that the internal structure
of a `Term` is well-formed and that it passes all of the rules of the
SAWCore type checker.

- `type : Term -> Type` returns the type of a particular `Term`, which
can then be used to, for example, construct a new fresh variable with
`fresh_symbolic`.

(loading-and-storing-terms)=
## Loading and Storing Terms

Most frequently, `Term` values in SAWScript come from Cryptol, JVM, or
LLVM programs, or some transformation thereof. However, it is also
possible to obtain them from various other sources.

- `parse_core : String -> Term` parses a `String` containing a term in
SAWCore syntax, returning a `Term`.

- `read_core : String -> TopLevel Term` is like `parse_core`, but
obtains the text from the given file and expects it to be in the simpler
SAWCore external representation format, rather than the human-readable
syntax shown so far.

- `read_aig : String -> TopLevel Term` returns a `Term` representation
of an And-Inverter-Graph (AIG) file in AIGER format.

- `read_bytes : String -> TopLevel Term` reads a constant sequence of
bytes from a file and represents it as a `Term`. Its result will always
have Cryptol type `[n][8]` for some `n`.

It is also possible to write `Term` values into files in various
formats, including: AIGER (`write_aig`), CNF (`write_cnf`), SAWCore
external representation (`write_core`), and SMT-Lib version 2
(`write_smtlib2`).

- `write_aig : String -> Term -> TopLevel ()`

- `write_cnf : String -> Term -> TopLevel ()`

- `write_core : String -> Term -> TopLevel ()`

- `write_smtlib2 : String -> Term -> TopLevel ()`
