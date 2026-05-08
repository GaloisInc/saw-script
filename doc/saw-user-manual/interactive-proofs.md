(interactive-proofs)=
# Interactive Proofs

:::{warning}
This section is under construction!
:::

## Transforming Term Values

The three primary functions of SAW are _extracting_ models (`Term`
values) from programs, _transforming_ those models, and _proving_
properties about models using external provers. We've seen how to construct
`Term` values from a range of sources. Now we show how
to use the various term transformation features available in SAW.

### Rewriting

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

### Folding and Unfolding

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

### Other Built-in Transformation and Inspection Functions

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
### Loading and Storing Terms

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

## Proofs about Terms

The goal of SAW is to facilitate proofs about the behavior of
programs. It may be useful to prove some small fact to use as a rewrite
rule in later proofs, but ultimately these rewrite rules come together
into a proof of some higher-level property about a software system.

Whether proving small lemmas (in the form of rewrite rules) or a
top-level theorem, the process builds on the idea of a _proof script_
that is run by one of the top level proof commands.

- `prove_print : ProofScript () -> Term -> TopLevel Theorem`
takes a proof script (which we'll describe next) and a `Term`. The
`Term` should be of function type with a return value of `Bool` (`Bit`
at the Cryptol level). It will then use the proof script to attempt to
show that the `Term` returns `True` for all possible inputs. If it is
successful, it will print `Valid` and return a `Theorem`. If not, it
will abort.

- `sat_print : ProofScript () -> Term -> TopLevel ()` is similar
except that it looks for a _single_ value for which the `Term` evaluates
to `True` and prints out that value, returning nothing.

- `prove_core : ProofScript () -> String -> TopLevel Theorem`
proves and returns a `Theorem` from a string in SAWCore syntax.

### Automated Tactics

The simplest proof scripts just specify the automated prover to use.
The `ProofScript` values `abc` and `z3` select the ABC and Z3 theorem
provers, respectively, and are typically good choices.

For example, combining `prove_print` with `abc`:

:::{code-block} console
sawscript> t <- prove_print abc {{ \(x:[8]) -> x+x == x*2 }}
Valid
sawscript> t
Theorem (let { x@1 = Prelude.Vec 8 Prelude.Bool
      x@2 = Cryptol.TCNum 8
      x@3 = Cryptol.PArithSeqBool x@2
    }
 in (x : x@1)
-> Prelude.EqTrue
     (Cryptol.ecEq x@1 (Cryptol.PCmpSeqBool x@2)
        (Cryptol.ecPlus x@1 x@3 x x)
        (Cryptol.ecMul x@1 x@3 x
           (Cryptol.ecNumber (Cryptol.TCNum 2) x@1
              (Cryptol.PLiteralSeqBool x@2)))))
:::

Similarly, `sat_print` will show that the function returns `True` for
one specific input (which it should, since we already know it returns
`True` for all inputs):

:::{code-block} console
sawscript> sat_print abc {{ \(x:[8]) -> x+x == x*2 }}
Sat: [x = 0]
:::

In addition to these, the `bitwuzla`, `boolector`, `cvc4`, `cvc5`, `mathsat`,
and `yices` provers are available. The internal decision procedure `rme`, short
for Reed-Muller Expansion, is an automated prover that works particularly well
on the Galois field operations that show up, for example, in AES.

In more complex cases, some pre-processing can be helpful or necessary
before handing the problem off to an automated prover. The
pre-processing can involve rewriting, beta reduction, unfolding, the use
of provers that require slightly more configuration, or the use of
provers that do very little real work.

### Proof Script Diagnostics

During development of a proof, it can be useful to print various
information about the current goal. The following tactics are useful in
that context.

- `print_goal : ProofScript ()` prints the entire goal in SAWCore
syntax.

- `print_goal_consts : ProofScript ()` prints a list of unfoldable constants
in the current goal.

- `print_goal_depth : Int -> ProofScript ()` takes an integer argument, `n`,
and prints the goal up to depth `n`. Any elided subterms are printed
with a `...` notation.

- `print_goal_size : ProofScript ()` prints the number of nodes in the
DAG representation of the goal.

### Rewriting in Proof Scripts

One of the key techniques available for completing proofs in SAWScript
is the use of rewriting or transformation. The following commands
support this approach.

- `simplify : Simpset -> ProofScript ()` works just like `rewrite`,
except that it works in a `ProofScript` context and implicitly
transforms the current (unnamed) goal rather than taking a `Term` as a
parameter.

- `goal_eval : ProofScript ()` will evaluate the current proof goal to a
first-order combination of primitives.

- `goal_eval_unint : [String] -> ProofScript ()` works like `goal_eval`
but avoids expanding or simplifying the given names.

### Other Transformations

Some useful transformations are not easily specified using equality
statements, and instead have special tactics.

- `beta_reduce_goal : ProofScript ()` works like `beta_reduce_term` but
on the current goal. It takes any sub-expression of the form `(\x -> t)
v` and replaces it with a transformed version of `t` in which all
instances of `x` are replaced by `v`.

- `unfolding : [String] -> ProofScript ()` works like `unfold_term` but
on the current goal.

Using `unfolding` is mostly valuable for proofs
based entirely on rewriting, since the default behavior for automated
provers is to unfold everything before sending a goal to a prover.
However, with some provers it is possible to indicate that specific
named subterms should be represented as uninterpreted functions.

- `unint_bitwuzla : [String] -> ProofScript ()`

- `unint_cvc4 : [String] -> ProofScript ()`

- `unint_cvc5 : [String] -> ProofScript ()`

- `unint_yices : [String] -> ProofScript ()`

- `unint_z3 : [String] -> ProofScript ()`

The list of `String` arguments in these cases indicates the names of the
subterms to leave folded, and therefore present as uninterpreted
functions to the prover. To determine which folded constants appear in a
goal, use the `print_goal_consts` function described above.

Ultimately, we plan to implement a more generic tactic that leaves
certain constants uninterpreted in whatever prover is ultimately used
(provided that uninterpreted functions are expressible in the prover).

Note that each of the `unint_*` tactics have variants that are prefixed
with `sbv_` and `w4_`. The `sbv_`-prefixed tactics make use of the SBV
library to represent and solve SMT queries:

- `sbv_unint_bitwuzla : [String] -> ProofScript ()`

- `sbv_unint_cvc4 : [String] -> ProofScript ()`

- `sbv_unint_cvc5 : [String] -> ProofScript ()`

- `sbv_unint_yices : [String] -> ProofScript ()`

- `sbv_unint_z3 : [String] -> ProofScript ()`

The `w4_`-prefixed tactics make use of the What4 library instead of SBV:

- `w4_unint_bitwuzla : [String] -> ProofScript ()`

- `w4_unint_cvc4 : [String] -> ProofScript ()`

- `w4_unint_cvc5 : [String] -> ProofScript ()`

- `w4_unint_yices : [String] -> ProofScript ()`

- `w4_unint_z3 : [String] -> ProofScript ()`

In most specifications, the choice of SBV versus What4 is not important, as
both libraries are broadly compatible in terms of functionality. There are some
situations where one library may outpeform the other, however, due to
differences in how each library represents certain SMT queries. There are also
some experimental features that are only supported with What4 at the moment,
such as `enable_lax_loads_and_stores`.

### Caching Solver Results

SAW has the capability to cache the results of tactics which call out to
automated provers. This can save a considerable amount of time in cases such as
proof development and CI, where the same proof scripts are often run repeatedly
without changes.

This caching is available for all tactics which call out to automated provers
at runtime: `abc`, `boolector`, `cvc4`, `cvc5`, `mathsat`, `yices`, `z3`,
`rme`, and the family of `unint` tactics described in the previous section.

When solver caching is enabled and one of the tactics mentioned above is
encountered, if there is already an entry in the cache corresponding to the
call then the cached result is used, otherwise the appropriate solver is
queried, and the result saved to the cache. Entries are indexed by a SHA256
hash of the exact query to the solver (ignoring variable names), any options
passed to the solver, and the names and full version strings of all the solver
backends involved (e.g. ABC and SBV for the `abc` tactic). This ensures cached
results are only used when they would be identical to the result of actually
running the tactic.

The simplest way to enable solver caching is to set the environment variable
[`SAW_SOLVER_CACHE_PATH`](saw-solver-cache-path-definition). With this environment variable set, `saw` and
`saw-remote-api` will automatically keep an [LMDB](http://www.lmdb.tech/doc/)
database at the given path containing the solver result cache. Setting this
environment variable globally therefore creates a global, concurrency-safe
solver result cache used by all newly created `saw` or `saw-remote-api`
processes. Note that when this environment variable is set, SAW does not create
a cache at the specified path until it is actually needed.

There are also a number of SAW commands related to solver caching.

- `set_solver_cache_path` is like setting `SAW_SOLVER_CACHE_PATH` for the
  remainder of the current session, but opens an LMDB database at the specified
  path immediately. If a cache is already in use in the current session
  (i.e. through a prior call to `set_solver_cache_path` or through
  `SAW_SOLVER_CACHE_PATH` being set and the cache being used at least once)
  then all entries in the cache already in use will be copied to the new cache
  being opened.

- `set_solver_cache_timeout` sets the cache's timeout (in microseconds) used
  for database lookups and inserts. The default timeout value is 2,000,000
  microseconds (2 seconds). This is a reasonably large timeout for most cache
  operations, but it may be convenient to increase this timeout for especially
  large proof goals.

- `clean_mismatched_versions_solver_cache` will remove all entries in the
  solver result cache which were created using solver backend versions which do
  not match the versions in the current environment. This can be run after an
  update to clear out any old, unusable entries from the solver cache. This
  command can also be run directly from the command line through the
  `--clean-mismatched-versions-solver-cache` command-line option.

- `print_solver_cache` prints to the console all entries in the cache whose
  SHA256 hash keys start with the given hex string. Providing an empty string
  results in all entries in the cache being printed.

- `print_solver_cache_stats` prints to the console statistics including the
  size of the solver cache, where on disk it is stored, and some counts of how
  often it has been used during the current session.

For performing more complicated database operations on the set of cached
results, the file `solver_cache.py` is provided with the Python bindings of the
SAW Remote API. This file implements a general-purpose Python interface for
interacting with the LMDB databases kept by SAW for solver caching.

Below is an example of using solver caching with `saw -v Debug`. Only the
relevant output is shown, the rest abbreviated with "...".

:::{code-block} console
sawscript> set_solver_cache_path "example.cache"
sawscript> prove_print z3 {{ \(x:[8]) -> x+x == x*2 }}
[22:13:00.832] Caching result: d1f5a76e7a0b7c01 (SBV 9.2, Z3 4.8.7 - 64 bit)
...
sawscript> prove_print z3 {{ \(new:[8]) -> new+new == new*2 }}
[22:13:04.122] Using cached result: d1f5a76e7a0b7c01 (SBV 9.2, Z3 4.8.7 - 64 bit)
...
sawscript> prove_print (w4_unint_z3_using "qfnia" []) \
                                  {{ \(x:[8]) -> x+x == x*2 }}
[22:13:09.484] Caching result: 4ee451f8429c2dfe (What4 v1.3-29-g6c462cd using qfnia, Z3 4.8.7 - 64 bit)
...
sawscript> print_solver_cache "d1f5a76e7a0b7c01"
[22:13:13.250] SHA: d1f5a76e7a0b7c01bdfe7d0e1be82b4f233a805ae85a287d45933ed12a54d3eb
[22:13:13.250] - Result: unsat
[22:13:13.250] - Solver: "SBV->Z3"
[22:13:13.250] - Versions: SBV 9.2, Z3 4.8.7 - 64 bit
[22:13:13.250] - Last used: 2023-07-25 22:13:04.120351 UTC

sawscript> print_solver_cache "4ee451f8429c2dfe"
[22:13:16.727] SHA: 4ee451f8429c2dfefecb6216162bd33cf053f8e66a3b41833193529449ef5752
[22:13:16.727] - Result: unsat
[22:13:16.727] - Solver: "W4 ->z3"
[22:13:16.727] - Versions: What4 v1.3-29-g6c462cd using qfnia, Z3 4.8.7 - 64 bit
[22:13:16.727] - Last used: 2023-07-25 22:13:09.484464 UTC

sawscript> print_solver_cache_stats
[22:13:20.585] == Solver result cache statistics ==
[22:13:20.585] - 2 results cached in example.cache
[22:13:20.585] - 2 insertions into the cache so far this run (0 failed attempts)
[22:13:20.585] - 1 usage of cached results so far this run (0 failed attempts)
:::

### Other External Provers

In addition to the built-in automated provers already discussed, SAW
supports more generic interfaces to other arbitrary theorem provers
supporting specific interfaces.

- `external_aig_solver : String -> [String] -> ProofScript ()`
supports theorem provers that can take input as a single-output AIGER
file. The first argument is the name of the executable to run. The
second argument is the list of command-line parameters to pass to that
executable. Any element of this list equal to `"%f"` will be replaced
with the name of the temporary AIGER file generated for the proof goal.
The output from the solver is expected to be in DIMACS solution format.

- `external_cnf_solver : String -> [String] -> ProofScript ()`
works similarly but for SAT solvers that take input in DIMACS CNF format
and produce output in DIMACS solution format.

### Offline Provers

For provers that must be invoked in more complex ways, or to defer proof
until a later time, there are functions to write the current goal to a
file in various formats, and then assume that the goal is valid through
the rest of the script.

- `offline_aig : String -> ProofScript ()`

- `offline_cnf : String -> ProofScript ()`

- `offline_extcore : String -> ProofScript ()`

- `offline_smtlib2 : String -> ProofScript ()`

- `offline_unint_smtlib2 : [String] -> String -> ProofScript ()`

These support the AIGER, DIMACS CNF, shared SAWCore, and SMT-Lib v2
formats, respectively. The shared representation for SAWCore is
described [in the `saw-script`
repository](https://github.com/GaloisInc/saw-script/blob/master/doc/extcore.md).
The `offline_unint_smtlib2` command represents the folded subterms
listed in its first argument as uninterpreted functions.

(finishing-proofs-without-external-solvers)=
### Finishing Proofs without External Solvers

Some proofs can be completed using unsound placeholders, or using
techniques that do not require significant computation.

- `assume_unsat : ProofScript ()` indicates that the current goal
should be assumed to be unsatisfiable. This is an alias for
`assume_valid`. Users should prefer to use `admit` instead.

- `assume_valid : ProofScript ()` indicates that the current
goal should be assumed to be valid.  Users should prefer to
use `admit` instead

- `admit : String -> ProofScript ()` indicates that the current
goal should be assumed to be valid without proof. The given
string should be used to record why the user has decided to
assume this proof goal.

- `quickcheck : Int -> ProofScript ()` runs the goal on the given
number of random inputs, and succeeds if the result of evaluation is
always `True`. This is unsound, but can be helpful during proof
development, or as a way to provide some evidence for the validity of a
specification believed to be true but difficult or infeasible to prove.

- `trivial : ProofScript ()` states that the current goal should
be trivially true. This tactic recognizes instances of equality
that can be demonstrated by conversion alone. In particular
it is able to prove `EqTrue x` goals where `x` reduces to
the constant value `True`. It fails if this is not the case.

### Multiple Goals

The proof scripts shown so far all have a single implicit goal. As in
many other interactive provers, however, SAWScript proofs can have
multiple goals. The following commands can introduce or work with
multiple goals. These are experimental and can be used only after
`enable_experimental` has been called.

- `goal_apply : Theorem -> ProofScript ()` will apply a given
introduction rule to the current goal. This will result in zero or more
new subgoals.

- `goal_assume : ProofScript Theorem` will convert the first hypothesis
in the current proof goal into a local `Theorem`

- `goal_insert : Theorem -> ProofScript ()` will insert a given
`Theorem` as a new hypothesis in the current proof goal.

- `goal_intro : String -> ProofScript Term` will introduce a quantified
variable in the current proof goal, returning the variable as a `Term`.

- `goal_when : String -> ProofScript () -> ProofScript ()` will run the
given proof script only when the goal name contains the given string.

- `goal_exact : Term -> ProofScript ()` will attempt to use the given
term as an exact proof for the current goal. This tactic will succeed
whever the type of the given term exactly matches the current goal,
and will fail otherwise.

- `split_goal : ProofScript ()` will split a goal of the form
`Prelude.and prop1 prop2` into two separate goals `prop1` and `prop2`.

### Proof Failure and Satisfying Assignments

The `prove_print` and `sat_print` commands print out their essential
results (potentially returning a `Theorem` in the case of
`prove_print`). In some cases, though, one may want to act
programmatically on the result of a proof rather than displaying it.

The `prove` and `sat` commands allow this sort of programmatic analysis
of proof results. To allow this, they use two types we haven't mentioned
yet: `ProofResult` and `SatResult`. These are different from the other
types in SAWScript because they encode the possibility of two outcomes.
In the case of `ProofResult`, a statement may be valid or there may be a
counter-example. In the case of `SatResult`, there may be a satisfying
assignment or the statement may be unsatisfiable.

- `prove : ProofScript SatResult -> Term -> TopLevel ProofResult`

- `sat : ProofScript SatResult -> Term -> TopLevel SatResult`

To operate on these new types, SAWScript includes a pair of functions:

- `caseProofResult : {b} ProofResult -> b -> (Term -> b) -> b` takes a
`ProofResult`, a value to return in the case that the statement is
valid, and a function to run on the counter-example, if there is one.

- `caseSatResult : {b} SatResult -> b -> (Term -> b) -> b` has the same
shape: it returns its first argument if the result represents an
unsatisfiable statement, or its second argument applied to a satisfying
assignment if it finds one.

### AIG Values and Proofs

Most SAWScript programs operate on `Term` values, and in most cases this
is the appropriate representation. It is possible, however, to represent
the same function that a `Term` may represent using a different data
structure: an And-Inverter-Graph (AIG). An AIG is a representation of a
Boolean function as a circuit composed entirely of AND gates and
inverters. Hardware synthesis and verification tools, including the ABC
tool that SAW has built in, can do efficient verification and
particularly equivalence checking on AIGs.

To take advantage of this capability, a handful of built-in commands can
operate on AIGs.

- `bitblast : Term -> TopLevel AIG` represents a `Term` as an `AIG` by
"blasting" all of its primitive operations (things like bit-vector
addition) down to the level of individual bits.

- `load_aig : String -> TopLevel AIG` loads an `AIG` from an external
AIGER file.

- `save_aig : String -> AIG -> TopLevel ()` saves an `AIG` to an
external AIGER file.

- `save_aig_as_cnf : String -> AIG -> TopLevel ()` writes an `AIG` out
in CNF format for input into a standard SAT solver.
