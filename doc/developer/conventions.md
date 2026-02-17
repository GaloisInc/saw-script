# SAW code conventions

Please read the Coding Style section of [../../CONTRIBUTING.md](CONTRIBUTING.md)
before kibitzing.

The (few) points specifically noted here are ones we generally have
broad alignment on.

## Imports of data type modules

It's common to have library modules (whether or not in the stdlib)
that provide a type, often a container type, and are named after that
type.
These are typically intended to be imported qualified, because
otherwise they generally conflict with `Prelude`.

Examples in the stdlib include `Data.Map` and `Data.Set`.

Modules of this flavor should, preferably, be imported like this:

```
import qualified Data.Map as Map
import Data.Map (Map)
```

That is, import the module under its name (in this case `Map`) rather than
something else (`M`, `Mp`, etc.) and also import the type name directly.
For `Data.Map` this makes the type available as `Map` and all the
operations available as e.g. `Map.keys`.
This pattern seems to produce the best available tradeoff of verbosity
vs. legibility.

If you only need one of these imports and not the other, it's reasonable to
comment it out with `--` rather than delete it, as the need for one vs. the
other has a tendency to shift frequently even with minor code changes and
retyping the imports over and over again gets very tedious.

## Prettyprinting vs. dumping

If you are printing a complicated value for human consumption, there
are (roughly speaking) two ways to do it:

- render it in a corresponding concrete syntax as legibly as possible
  (prettyprinting)

- render it in a schematic form that does not gloss over details and
  reports exactly what's present (dumping)

For example, error messages that display values or expressions will
want to prettyprint them; however, if for example you want to examine
the internal representation before typechecking while chasing a
typechecker bug, you probably want the dump output.
That these are different is often overlooked, and people often use
prettyprinters for both; however, for SAW we would in general like to
have both available, so we have two corresponding sets of
infrastructure.
(As of this writing the dump infrastructure hasn't been built out yet;
but that is expected to happen soon.)

We don't use the `Show` class or `show` functions for either of these
roles, for various reasons.
See [pretty.md](pretty.md) for further discussion.

## Naming conventions for prettyprinting

We have established, or are in the process of establishing, the
following convention for prettyprinting functions:

- to print a `Foo` to a `Doc`, the function is called `prettyFoo`;
- to print a `Foo` to `Text`, the function is called `ppFoo`.

(As of this writing many of the `ppFoo` functions produce `String` for
legacy reasons. This will get cleaned up over time.)

There are `Pretty` instances (so you can call `pretty` to get a `Doc`)
for some types.
However, in SAW, many types, including foundational ones like the
SAWCore `Term`, require extra arguments and/or monads to print
properly.
Also, declaring `Pretty` instances requires either stuffing the
printing code in with the type declarations, which is undesirable for
complex ASTs, or arguing with the compiler about orphan instances,
which is a headache, so the path of least resistance is to mostly
not use `Pretty` instances.
By default, you should reach for `prettyFoo` or `ppFoo` to print; that
will be the recommended path and take the necessary arguments to get
the recommended output.
In cases where that function is monadic and you absolutely cannot
afford to be in a monad, there will generally be an alternate
`prettyFooPure` and `ppFooPure` you can use; however, in general these
produce degraded output and should not be used except when absolutely
necessary.

Then, the proper way to render a `Doc` to text is with the `render`
functions in `SAWSupport.Pretty`.
These take a `PPOpts` value that holds the user's prettyprinting
settings.
(In general prints should honor those settings, so prints should be
rendered using them.
Therefore, please avoid using `show` to render prettyprinter docs.)

As of this writing the `render` functions are:

- `render` produces `String`
- `renderText` produces `Text`

At some point we expect to change these so `Text` is the default.

Also, do not use `show` or `Show`-related functions for user-facing
prints.
(Certain parts of the code that haven't been cleaned out yet may not
have any other choices, but that is expected to improve over time.)

Note that SAW's naming convention differs from Cryptol's, where `pp`
functions produce `Doc`.
In SAW we generally need ready access to both the `Doc` and `Text`
forms, so we need two sets of names, and the convention we have
chosen best matches existing practices.

To print Cryptol values, import `CryptolSAWCore.Pretty`
(conventionally qualified as `CryPP`) and use `CryPP.pp` to print to
`Text` and `CryPP.pretty` for a Doc.
This avoids both the naming confusion and also various technical
issues interfacing the printers.

For further discussion of all these points, see [pretty.md](pretty.md).

## Naming conventions for dumping

As of this writing the dump interface is stil being figured out, so
this hasn't been determined yet.
