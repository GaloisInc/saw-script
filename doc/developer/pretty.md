# Prettyprinting and dumping in SAW

This document outlines a number of points about converting values to
strings.
Most of the main points are introduced elsewhere, e.g. in
[conventions.md](conventions.md); this document is here to go into
more detail and provide rationale.


## Prettyprinting vs. dumping

"Prettyprinting" is the act of converting a value of some type,
typically some kind of compiler AST element, to a human-readable
string.
Prettyprinting normally involves reproducing the corresponding
concrete syntax (at least to some extent); it also tries to avoid
generating excess goo, like unnecessary parentheses, that makes the
output harder to read; and it introduces formatting and layout that
isn't natively present in the AST.

"Dumping", by contrast, is the act of converting a value of some
type, again typically some kind of compiler AST element, to a
string in a schematic format that accurately reflects the exact
structure of the value.
Dumping involves introducing formatting, but formatting that reflects
the hierarchical/recursive structure of the AST rather than any
concrete syntax.
The general idea is to output an indented text tree that can still
be examined by a human but also accurately reflects the internals.

These two functions have different purposes, but are often conflated.
Trying to use one for the other eventually leads to problems.

It's common for prettyprinter output to fold together similar but
not quite identical internal states in the name of readability or
adherence to concrete syntax.
Dump output specifically doesn't do that.

For example, suppose you have the abstract syntax
   ```
   data Expr = Num Int | Var Text | Add Expr Expr
   ```
and you have the values
   ```
   Add (Num 3) (Add (Num 4) (Var "x"))
   Add (Add (Num 3) (Num 4)) (Var "x")
   ```

A typical prettyprinter will render both of these as `3 + 4 + x`.
This is fine if for example you want to print
   ```
   Type mismatch: found String, expected Int
   In the expression "x"
   In the expression "3 + 4 + x"
   ```

However, if you're chasing a bug where your constant-folding pass is
mysteriously skipping some cases, you may in fact care a great deal
about the exact representation and the prettyprinter output won't
be illuminating.
(Or worse, it may lead you to look past the problem.)
Instead, you want to dump the expression, which in SAW's dump style
will print something like this:

   ```
   Add
      Num 3
      Add
         Num 4
         Var x
   ```
and
   ```
   Add
      Add
         Num 3
         Num 4
      Var x
   ```
respectively.

There's a fairly strong tendency for weird problems to exist in
exactly the places that prettyprinters tend to gloss over.
(This is only natural; it's because both the prettyprinter and the bug
are informed by the way humans think about the AST.)

People sometimes use default/derived `Show` instances as a proxy for
real dumps, because they do report the exact representation.
However, for expressions more complicated than this they become
completely illegible very quickly, because they're restricted to a
single line of output and don't make any particular effort at
legibility.
(In fact, the primary goal of default `Show` instances is that the
text can be read back with the corresponding default `Read` instance,
which is all very well but not very helpful for human readers.)

For these reasons SAW has (or is getting) infrastructure for both
prettyprinting and dumping.


## Prettyprinting in SAW

### Availability of prettyprinting

Prettyprinting infrastructure should be available for all nontrivial
types anywhere in SAW that are of any user-facing interest.
(This includes anything that might reasonably appear in an error or
warning message.)
Currently, it isn't always.
If you need prettyprinting for some type and it isn't there, add it,
or if you don't have time, get someone else to.
If you hack together a starter implementation (as described below),
and "someone" should fix it up later, merge what you've got and open
an issue.
It's better to have a bodgy printer than none.
Don't use `show` as a substitute, and don't refrain from printing
things that should be printed (e.g. in error messages) because the
infrastructure is missing.

### Naming conventions for prettyprinting

As explained in [conventions.md](conventions.md) the naming convention
for prettyprinting functions is:

- to print a `Foo` to a `Doc`, call `prettyFoo`
- to print a `Foo` to text, call `ppFoo`

("text" here meaning either `Text` or `String` depending on
circumstances; the goal is to move it all to `Text`, but that'll take
a while.)

The intent is to provide both versions for all relevant types `Foo`.
(Since in general the text version just calls the `Doc` version,
providing both does not introduce huge overheads.)

We want both in SAW because, first, obviously in general
prettyprinting anything that contains a `Foo` wants to be able to
print it to a `Doc`.
But also, SAW is full of error paths and error cases that need to
print complex internal objects.
Much of this code is dodgy and squirrelly, and we don't want to
introduce complications or barriers to improving it.
Some error messages will end up being prettyprinter docs, but most
won't.

Error messages have a tendency to occur in deeply nested places in the
code where the amount of text space available to generate the message
is limited.
Extraneous calls and conversions take space interfere with fitting the
message in and with the readability of the error path code, and all of
this serves to discourage writing complete and clear error messages
that print all the relevant information.
The extra width needed for to call `render` on a `Doc` is not small
since `render` needs to be passed the prettyprinting options;
therefore we should in general provide a text-based interface as well
as the `Doc` one.

There's an additional complication in SAW, which is that some printing
functions require additional arguments or run in monads.
This more or less rules out typeclass-based approaches, as explained
in more detail below.

The preferred printers for a `Foo` are always `prettyFoo` and `ppFoo`.
Where that's monadic, there will normally also be non-monadic versions
`prettyFooPure` and `ppFooPure`.
These should, however, only be used when absolutely necessary as they
will result in degraded output.

### Additional arguments and monads for prettyprinting

For good or ill, SAW has a collection of user-settable printing options.
These are collected in a type `PPOpts` in `SAWSupport.Pretty` and
mostly, though not entirely, affect the SAWCore prettyprinter.
The consequence of this, though, is that the SAWCore prettyprinter and
everything else that ultimately recurses into the SAWCore
prettyprinter needs the current printing options value.
Some prints use the default options instead, but every such instance
is a bug -- we should honor the user settings.

The SAWCore prettyprinter also needs access to the SAWCore naming
environment to print nicely.
Basically, it checks the naming environment to allow printing the
smallest unique form of every identifier rather than a fully
module-qualified name.
This means that the SAWCore prettyprinter, and everything that
ultimately recurses into the SAWCore prettyprinter, needs either an
explicit naming environment (which is not readily available outside
the SAWCore library) or needs the SAWCore `SharedContext` and needs to
run in `IO` in order to be able to retrieve the naming environment.

There are alternate entry points not in `IO` that use a default
(empty) environment, but these produce degraded output and in
user-facing prints that's a bug.
(For example, see
[issue #2802](https://github.com/GaloisInc/saw-script/issues/2802).)
Consequently, we should avoid using these and, in the long run,
ideally we'd remove them.

(We could in principle restructure the way the SAWCore library works
so it would be some other monad and not necessarily `IO`, but that
would be expensive and serve little purpose.
Forcing all callers to extract the naming context from the
`SharedContext` in advance and pass it explicitly creates a larger
burden and defeats the purpose of using monads to manage state.
Monadically-tainted printing is not going away unless something
substantial changes in SAWCore.
There is some hope of being able to make it simpler and more
systematic in the long run though.)

Note that the `SharedContext` does not contain a copy of the `PPOpts`
so it has to be passed around explicitly.  This might change, because
there are a lot of places in lower levels of the system where it isn't
otherwise available and, as noted, printing without it isn't
desirable.

### The prettyprinting options

The `PPOpts` type defined in `SAWSupport.Pretty` has the following
members:

- `ppUseAscii`, which is a Cryptol prettyprinter setting that's
  supposed to be propagated to all Cryptol prints.

- `ppBase`, which controls whether integers are printed in decimal or
  hex or maybe octal.
  (Or for users who are nuts, some other integer base up to 36...)
  This is also supposed to be propagated to Cryptol prints.

- `ppColor`, which controls the generation of angry fruit salad.

- `ppMaxDepth`, which optionally limits the recursion depth for printing
  SAWCore terms.

- `ppNoInlineMemoFresh`, which is used by the `print_goal_inline` SAWScript
  command to fine-tune the SAWCore printing.

- `ppMemoStyle`, which picks one of three ways to display SAWCore memoization
  variables.

- `ppMinSharing`, which controls how many occurrences of a SAWCore
  subterm must appear to memoize it with a let-binding when printing.

### Why not `Pretty`?

The `Prettyprinter` package does provide a `Pretty` class with a
`pretty` function that we could in principle make broader use of.
We generally don't, and we haven't made our own either, for two
reasons:

First, as discussed above many printing functions in SAW require
additional arguments or monads that are not part of the class
signature.
These are also by no means all uniform, and the objects that one needs
to print some types are not readily available when one needs to print
others, so it would be difficult to define any one signature in a
typeclass.

Second, declaring instances requires either stuffing them in with the
type declarations or arguing with the compiler about orphan instances.
Both of these are a headache: for a complex AST it's really preferable
to not have extraneous stuff in the same module with it, and also,
prettyprinter code is most conveniently and legibly written in a
module context where one can import all the prettyprinter combinators
and widgets without worrying about name conflicts with other things.
Then on the other hand there are reasons the compiler complains
about orphan instances.
(Even if some of those reasons seem to be bugs or weaknesses in GHC or
in the formulation of Haskell typeclasses, these are the tools we
have.)

The path of least resistance, given both these points, is to not
bother with typeclasses and adopt a naming convention instead.

### Why not `Show`?

The `Show` class and `show` functions are not well suited for either
prettyprinting or dumping, at least in SAW.
There are a number of reasons for this.

First, as discussed above many printing functions in SAW require
additional arguments or monads that are not part of the signature
of `Show`; this makes the class itself of limited value, similar
to `Pretty`.

Second, `Show` is based on `String` and we want to be using `Text`.
One could conceivably use a `Text`-based replacement for `Show`, but
given the other considerations this isn't particularly compelling.

Third, compiler-generated default `Show` instances do not print
adequate output except for the simplest types.
For prettyprinting, this is obvious.
For dumping, it is less so, and at least a default `Show` instance
does print exactly what the value is without abstracting away details
you might care about.
(Which is the whole point of having separate dump infrastructure.)
However, the output of default `Show` instances for even moderately
complex types is still completely unreadable.
The schematic indenting dump form that SAW's dump infrastructure
uses/is intended to use falls down on extremely large values, but
scales much better and is much more legible before it hits those
limits.

Fourth, SAW's codebase is full of legacy `Show` instances, mostly of
low quality, and also full of uses of them in unexpected places.
Until all this is rooted out it's better to not also be trying to use
`Show` for anything useful.

We have decided not to _remove_ `Show` instances outright, at least
for the time being.
Until the dump infrastructure is fully built out, sometimes `Show`
will be necessary for debug prints.
Because of the transitive nature of these interfaces, to have a
`Show` instance for a high-level type you must also have `Show`
instances for all lower-level types involved in it.
So if you want `Show` for a debug print of some high-level type
it's important for all the underlying `Show` instances to exist.
However, ideally all these `Show` instances would be defined in terms
of dump.

Apart from this explicit support for debug prints and the limited
approved uses (in the next section), `Show` should be considered
deprecated in SAW.

### Acceptable use of default (derived) `Show` instances

It is reasonable to derive a default `Show` instance and define the
prettyprinting and/or dumping logic for it in the following cases:

- Types that are plain enumerations and where the Haskell-facing
spelling of the constructors (capitalized and all) is an acceptable
user-facing spelling.

- Types that are otherwise acceptable but where some constructors may
have arguments of a simple base type (e.g. `Bool`, `Int`), or lists of
same expected to be short, where the output syntax generated by the
derived `Show` instance remains acceptable for user-facing prints.

- For dump only, types that are otherwise acceptable and where the
arguments are short/small/simple enough that the output generated by
the derived `Show` instance (which will always be on one line) is
reasonably short so it _fits_ on that line, and doesn't have more than
one or maybe two layers of nesting symbols.

Otherwise, write at least a dump instance.

### Cribsheet for prettyprinting

Writing prettyprinter code is ... not necessarily tedious but somewhat
involved.
One tends to need to open the 
[prettyprinter library docs](https://hackage.haskell.org/package/prettyprinter/docs/Prettyprinter.html)
and dig around.
Also, since one doesn't do it very often this process generally needs
to be repeated every time the issue comes up, which increases the
effort required (and even more, the _perceived_ effort required).

Meanwhile, writing prettyprinter code for nontrivial types with
nontrivial syntax that does things like indenting and that generates actually pretty
output takes real work.

It's often not necessary to write a _good_ prettyprinter
implementation up front, just a starter one.
The following will get you an adequate but not great starter:

- Import `Prettyprinter`.

- Turn on `OverloadedStrings` if you haven't already.

- First, write the necssary `prettyFoo` skeletons with cases for each
  constructor and so forth.
  Then write the cases according to the remaining steps.

- Call the appropriate `prettyFoo` functions for subelements.

- Use `text` to convert any explicit `Text` values (e.g. identifier
  names) to `Doc`.

- String literals are already `Doc` when they need to be.

- Stick the elements together into output like you would if you were
  generating `Text`: use `<>` to paste pieces together, use `concat`
  or `intercalate` for lists, and perhaps use `unlines` on a list of
  lines for multiline output.

- Replace the list/text combinators with prettyprinter ones as follows:
  - `concat` becomes `hcat`.
  - `intercalate` becomes `hcat $ intersperse`.
  - `intercalate` that inserts spaces can just be `hsep`.
  - `unlines` becomes `vsep`.
  - If you have `<>` with an explicit space on either side, remove the
    space and replace `<>` with `<$>`.
  - You can replace explicit leading spaces on a line with `indent n` for
    the appropriate constant `n`.

- Currently `x <+> y <+> z` will generate two spaces between `x` and `z`
  if `y` comes out empty, e.g. when it's a list and the list is empty.
  This is a headache to deal with, so for a starter version just mark it
  for later attention.
  (The best available approach seems to be to write `x <> y <+> z` and
  build `y` with a variant `hsep` that prepends `emptyDoc` with `<+>`
  when the list isn't empty.)

- If at this point, having gotten started, you feel like finishing the
  job, certainly go ahead.
  Otherwise, if (as is likely) the output is not everything one would
  wish, open an issue to track the technical debt and move on.

- The Rocq AST prettyprinter in saw-core-coq's Language.Coq.Pretty is a
  decent place to crib from.
  Avoid cribbing from either the SAWCore or SAWScript prettyprinting
  logic until further notice; as of this writing both are in a pretty
  dismal state.


## Dumping in SAW

The dump infrastructure hasn't been built out yet, so this is still
theoretical.

The plan is for every nontrivial type `Foo` to have a dumper function
`dumpFoo` that returns a prettyprinter document in the recommended
schematic form.
There will be infrastructure so writing these functions takes very little
effort.

The primary consumer of the dump interface is intended to be explicit
dump points in the system, where you can tell SAW to dump the internal
representation and it will do so.

However, one will sometimes want dump output in debug prints.
It isn't clear at the moment if we should have a second dump function
for every type that produces `Text`, and if so what to call it.
(`ddFoo`? that's not so wonderful...)
For debug prints, `show $ dump foo` may be sufficient -- there is no
need to worry about rendering options.
(However, that produces `String`, so in many cases it will end up
being `Text.pack $ show $ dump foo`, and every extra widget like that
in the common-case call chain is an extra annoyance.)
