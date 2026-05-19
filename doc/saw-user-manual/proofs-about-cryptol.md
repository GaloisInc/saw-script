# Proofs about Cryptol Models

Cryptol is a modeling and specification language for cryptographic
algorithms.
It is integrated into SAW and used for a broad range of tasks.
Use of SAW for essentially any purpose requires use of Cryptol.
Thus, the
[Cryptol manual](https://galoisinc.github.io/cryptol/master/RefMan.html)
is an important additional resource for SAW users.

In this chapter we discuss how to import Cryptol models and prove
properties about them.

## Importing Cryptol

Cryptol modules can be imported with `import`.
For example:

```sawscript
import "Foo.cry";
```

The name to import can be a filename in double quotes, or a Cryptol
module name, possibly qualified with `::`, _without_ quotes.
The environment variable `CRYPTOLPATH` is used to search for Cryptol
modules.
SAW uses the same code to do this as Cryptol itself, so the behavior
should be the same, including in complicated cases.

There is a known problem with the interaction of pathnames in quotes
with `CRYPTOLPATH`, which also happens on the Cryptol command line;
see [#2194](https://github.com/GaloisInc/saw-script/issues/2194).
This can be avoided by using qualified module names instead of file
paths.

For example, instead of

```sawscript
import "Foo/Bar.cry";
```

use

```sawscript
import Foo::Bar;
```

To import a submodule (Cryptol submodules are ML-style modules nested
within source files), use the keyword `submodule` before the module
path.

By default the contents of the imported module are placed in scope.
If this isn't what you want, you can use the keyword `as` to introduce
a qualified name.

After

```sawscript
import Foo::Bar as Baz;
```

the contents of the module `Foo::Bar` are available under the name
`Baz`; e.g. `Foo::Bar::myfunc` appears as `Baz::myfunc`.

It is also possible to restrict the set of symbols imported.
A list of symbols in parentheses after the rest of the import
restricts the import to the symbols named; others are hidden.
Alternatively, a list with the keyword `hiding` hides the listed
symbols and imports the rest.

For example,

```sawscript
import Foo::Bar as Baz hiding (myfunc);
```

prevents referring to `Baz::myfunc`.

Partial imports are often useful to reduce namespace pollution or
avoid name conflicts.

There is an additional mechanism `cryptol_load`, which is almost but
not quite equivalent to `import ... as`.

The syntax `Baz <- cryptol_load "Foo/Bar.cry";` is comparable to
`import "Foo/Bar.cry" as Baz;` with one important difference: the
returned handle `Baz` is a first-class value and can be passed to
SAWScript functions if doing complicated things.
In the `import` form that does not work; it can be used as a module
qualifier only.
Eventually the `import` form will become equivalent, at which point
`cryptol_load` will be deprecated.

Note that `cryptol_load` does not support qualified module names or
partial imports.
Also, if using it for complicated things, beware of
[issue #3167](https://github.com/GaloisInc/saw-script/issues/3167);
currently if you pass a module handle function to a function defined
before the module load, things get confused and the Cryptol importer
panics.

## Writing Cryptol Inline in SAWScript

Typically, complex or nontrivial models will be written as one or more
external Cryptol modules and imported into SAW.
However, it isn't necessary to create a whole Cryptol module for a few
simple definitions.
The quasiquotation syntax `{{ expr }}` allows embedding a Cryptol
expression directly into SAWScript.
We have already seen this in the introductory examples.

If you want to refer to a Cryptol type, the syntax for that is
`{| Ty |}`.

You can also use the syntax `let {{ decls }};` anywhere the SAWScript
`let decl;` form can appear, which lets you write a Cryptol-level
declaration, or possibly several of them.

<!--
   XXX: expand on what that means and how it's different from
   SAWScript-level bindings once we get the binding and scoping
   semantics straightened out.
-->

<!-- XXX: describe how you do this in the python interface -->

## Semantics of Imports

All Cryptol imported, or introduced by quasiquotation, is translated
into SAWCore.
(Recall that SAWCore is SAW's internal interchange and proof
language.)

This is done at the point in SAWScript execution where the import or
quasiquotation block occurs.
Unless doing complex things in SAWScript (discussed
[later](#sawscript)), the primary consequence of this is that type
errors and even syntax errors in embedded Cryptol are not detected
until "runtime".
This can be annoying.
However, it allows, within certain restrictions, Cryptol numeric
types to be chosen at "runtime" rather than being fully constant;
this in turn allows constructing more flexible proofs than would
otherwise be possible.

## Semantics of Quasiquotation Blocks

Embedded Cryptol blocks can refer to elements from imported Cryptol
modules (complete with module qualifiers where needed, etc.)
However, they can _also_ refer to the following other things from
the surrounding SAWScript:

- Values whose SAWScript type is `Term`, regardless of where they came
  from, as long as they have an underlying SAWCore type that can be
  represented in Cryptol; this includes e.g. values from non-Cryptol
  importers.

- Values whose SAWScript type is `Type`, regardless of where they came
  from, as long as they have a kind (type of type) that can be represented in
  Cryptol.
  These appear as Cryptol types.

- SAWScript integers.
  These appear as Cryptol numeric types.
  If you want to use one as a Cryptol numeric value, you can lower it
  with `` ` `` in your Cryptol expression, as usual in Cryptol.

- SAWScript boolean and string values appear as Cryptol boolean and
  string values.

Currently because SAW strings are Unicode and Cryptol strings are
bytes, the translation of strings is unsatisfactory.
This will almost certainly change in the future.

Unfortunately, due to internal restrictions, when an element cannot be
made available in the Cryptol environment because its type is
unsuitable, its name just disappears and references to it fail without
any direct explanation.
If you think something should be visible from Cryptol and it isn't,
check its type.

## Stating Proof Goals

A proof goal can be any well-typed Cryptol expression that produces
a boolean.
(It can, but need not be, something specifically declared as a
property in Cryptol.)
The convention in Cryptol is that quantified proof goals are expressed
as lambdas (that is, functions) rather than having forall-quantified
types in Cryptol syntax.
The operator for implication is `==>`.
Thus, for example, to prove that addition of integers respects
less-than, the proof goal would be

```cryptol
{{ \(x : Integer) -> \y -> x < y ==> x + 1 < y + 1 }}
```

or equivalently

```cryptol
{{ \(x : Integer) y -> x < y ==> x + 1 < y + 1 }}
```

Beware that if you don't specify the types when writing such a goal,
the resulting goal may be polymorphic (for example, in this case it
will range over all types in Cryptol `Num`) and then solvers will
refuse to handle it.

Also beware that if you misspell the type name, Cryptol will assume
you intended to introduce a type variable, with the same result.

## Proving Things

The basic mechanism for proving Cryptol proof goals is the
SAWScript function `prove_print`:

```sawscript
prove_print z3 {{ \(x : Integer) -> \y -> x < y ==> x + 1 < y + 1 }};
```

It takes two arguments; the second is the goal, which will usually be
a Cryptol expression in double-braces as shown here, and the first is
a proof script.

Unless using the manual proof interface, which is still largely
experimental and not really recommended for other than advanced users
(see [Interactive Proofs](#interactive-proofs)), the proof scripts
you'll be using will be solver invocations.

The `prove_print` function fails (returning to the REPL if interactive
and exiting with failure if not) if the proof does not succeed.
Beware: a SAWScript function `prove` also exists.
It returns a success/failure value, rather than failing; accidental
use of `prove` instead of `prove_print` can result in proofs failing
more or less silently.
(At some point `prove` will be deprecated to remove this footgun; in
the meantime, be careful.)

(using-solvers)=
## Using Solvers

The basic proof scripts are just solver names.
For example, the `z3` proof script runs the Z3 theorem prover, the
`abc` proof script runs the ABC prover, and the `cvc5` script runs
the CVC5 solver.
All of these are reasonable choices.

Others supported by SAW include Bitwuzla (`bitwuzla`), Boolector
(`boolector`, deprecated because it's been replaced upstream by
Bitwuzla), MathSAT (`mathsat`), and Yices (`yices`).
There is also an internal solver/decision procedure called `rme`
that uses Reed-Muller expansions.

The question of which solver to use is fundamentally unanswerable:
they are all different internally, and handle different sets of things
well, and it's extremely difficult to characterize those sets from
outside.

The best general guidance we can offer is: if one doesn't work, or
takes excessively long to run or runs out of memory, try another.

There are a couple specific points worth mentioning:

- A lot of people reach for `z3` by default, which is as much because
  it's better known than for any particular other reason.
  At one point it had broader coverage of theories than others; that
  is not true so much any more.
  This does not make it a _bad_ choice; but sometimes, others are
  faster.

- Bitwuzla (and Boolector before it) are specialized to bitvectors
  and don't support integers (integers in the "math integer" and
  Cryptol `Integer` type sense) or many other theories; however,
  proofs near code tend to involve a lot of bitvectors and sometimes
  this is what you want.

- The internal `rme` solver is based on an algorithm that specifically
  handles chains of exclusive-or efficiently, rather than (as often
  happens) expanding it in terms of plain and/or.
  This makes it work particularly well on the Galois field operations
  that show up, for example, in AES.

Also be aware that different versions of the same solver often also
perform differently on any given proof, and newer versions are not
always better.

Ultimately, the reason SAW supports so many solvers is that the only
real way to deal with the question of which solver to use is to punt
it to the user.

### Further Solver Scripts

There is also a collection of additional solver scripts that run the
solvers in slightly different ways.

The general form of these is

```sawscript
[offline_][LIBRARY_][unint_]SOLVER[_VARIANT]
```

The `LIBRARY` part can be either `sbv` for the `SBV` solver interface
library or `w4` for the `what4` solver interface library.
Neither of these is better nor worse; they're just different.
Using one or the other can occasionally unstick a proof that otherwise
runs forever, or avoid a particular idiom that causes one of the
solvers to complain or fail.
Note that the default interface library if not requested specifically
can vary; check the help text for each function with the `:h` REPL
command if in doubt.

The `unint` fragment, when present, indicates a proof script that
takes an additional argument, which is a list of names to be treated
as uninterpreted.
See the next section for further discussion.

The `offline` fragment, when present, indicates a proof script that
takes a filename as an additional argument.
Instead of running the solver, SAW will dump the solver query out to
the file.
This can be used to inspect the solver query as well as to run the
solver by hand; the latter can be useful if you want to experiment
with solver options or different solver versions or other things SAW
does not provide good direct access to.
Note that while all solvers theoretically speak SMTlib, each has its
own dialect, so the offline output for each solver will be slightly
different.
Also note that the offline solver tactics always succeed; they assume
you will run the solver yourself and the proof will work.

Not all combinations exist; in particular the offline tactics
use `what4` and generally also include `unint_`.

Use `:search ProofScript` or `:search (_ -> ProofScript ())` to find
everything that exists.
(The second form excludes things like `prove_print` that take proof
scripts.
Both forms will also show you interactive proof tactics, especially if
you have enabled experimental features.)

If you find that a combination you want to use is missing, please
file a bug report.

## Uninterpreted Functions

The most common technique to make a solver proof go faster is to mark
certain functions as uninterpreted.
This hides the implementation of a function.
In fact, it replaces it with an arbitrary function where the only
thing we know about it is that it _is_ a function in the math sense:
given the same argument, it produces the same result.
This prevents the solver from wasting time exploring the definition.
Note that this is a generalization of the proof goal: it replaces a
goal that asks for something to be true about a specific function with
one that asks for it to be true about all functions.
So it's a safe transformation.

This is an extremely helpful thing to do in many cases when reasoning
about an equivalence that has same function appearing on both sides.
It's very common that the function will also have the same
argument on both sides, and that if it doesn't, it's wrong.
In this case, preventing the solver from looking inside the function
can save a lot of time.

Even though, arguably, converting a function to uninterpreted should
be its own interactive proof tactic separate from (and used prior to)
running a solver, it is common enough, especially in proofs about
cryptographic code, that these compound proof scripts have been set
up.

## Satisfiability

SAW can also do satisfiability queries as well as proofs.
The command is `sat_print`; it is used essentially the same way
as `prove_print`.
(There is also a `sat` that is, like `prove`, generally
best avoided.)
On success it prints the satisfying assignment found.

For example:

```console
sawscript> sat_print z3 {{ \(x : Integer) (y : Integer) -> x < y }}
Sat: [
x = 0
y = 1
]
```

In the case of `prove_print` the goal is read "for all `x` and `y`...";
here it's read "exists `x` and `y` such that...".

There is, alas, currently no good way to state goals that require
quantifier alternation.
Since solvers cannot in general handle them, this is not a huge
limitation in practice.
