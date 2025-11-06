# About `mir-json`

We are interested in verifying code written in Rust, but Rust is an extremely
rich programming language that has many distinct language features. To make the
process of verifying Rust simpler, SAW targets an intermediate language used in
the Rust compiler called [MIR](https://blog.rust-lang.org/2016/04/19/MIR.html)
(short for "Mid-level IR"). MIR takes the variety of different features and
syntactic extensions in Rust and boils them down to a minimal subset that is
easier for a computer program to analyze.

The process of extracting MIR code that is suitable for SAW's needs is somewhat
tricky, so we wrote a suite of tools called `mir-json` to automate this
process.  `mir-json` provides a plugin for tools like `rustc` and `cargo` that
lets you compile Rust code as you normally would and produce an additional
`.json` file as output. This `.json` file contains the MIR code that was
produced internally by the Rust compiler, with some additional minor tweaks to
make it suitable for SAW's needs.

`mir-json` is not a single tool but rather a suite of related tools that
leverage the same underlying plugin. For SAW purposes, the two `mir-json` tools
that are most relevant are:

* `saw-rustc`: A thin wrapper around `rustc` (the Rust compiler), which is
  suitable for individual `.rs` files.
* `cargo-saw-build`: A thin wrapper around the `cargo build` command, which is
  suitable for `cargo`-based Rust projects.

Most of the examples in this tutorial involve self-contained examples, which
will use `saw-rustc`. Later in the tutorial, we will examine a Salsa20 case
study that involves a `cargo`-based project, which will use `cargo-saw-build`.

## A first example with `saw-rustc`

Let's try out `saw-rustc` on a small example file, which we'll name
`first-example.rs`:

:::{literalinclude} code/first-example.rs
:language: rust
:::

This is the identity function, but specialized to the type `u8`. We can compile
this with `saw-rustc` like so:

:::{code-block} console
$ saw-rustc first-example.rs
<snip>
note: Emitting MIR for first_example/abef32c5::id_u8

linking 1 mir files into first-example.linked-mir.json
<snip>
:::

`saw-rustc` prints out some additional information that `rustc` alone does not
print, and we have displayed the parts of this information that are most
interesting. In particular:

* `saw-rustc` notes that is is `Emitting MIR for first_example/abef32c5::id_u8`,
  where `first_example/abef32c5::id_u8` is the full _identifier_ used to uniquely
  refer to the `id_u8` function. It's entirely possible that the `abef32c5`
  bit will look different on your machine; we'll talk more about identifiers in
  the "Identifiers" section.
* Once `saw-rustc` produced a MIR JSON file named
  `first-example.linked-mir.json`. This is an important bit of information, as
  SAW will ingest this JSON file.

If you'd like, you can inspect the `first-example.linked-mir.json` file with
JSON tools (e.g., [`jq`](https://jqlang.github.io/jq/)), but it is not
important to understand everything that is going on there. This is
machine-generated JSON, and as such, it is not meant to be particularly
readable by human eyes.

(saw-rust-lib-path-env-var)=
## The `SAW_RUST_LIBRARY_PATH` environment variable

Rust has a large set of standard libraries that ship with the compiler, and
parts of the standard library are quite low-level and tricky. SAW's primary
objective is to provide a tool that can analyze code in a tractable way. For
this reason, SAW sometimes needs to invoke simplified versions of Rust standard
library functions that are more reasonable for an SMT-based tool like SAW to
handle. These simplified functions are equivalent in behavior, but avoid using
problematic code patterns (e.g., gnarly pointer arithmetic or the
[`transmute`](https://doc.rust-lang.org/std/intrinsics/fn.transmute.html)
function).

If you are only ever compiling self-contained pieces of code with `saw-rustc`,
there is a good chance that you can get away without needing to use SAW's
custom version of the Rust standard libraries. However, if you ever need to
build something more complicated than that (e.g., the Salsa20 case study later
in this tutorial), then you _will_ need the custom libraries. For this reason,
it is worthwhile to teach SAW the location of the custom libraries now.

At present, the best way to obtain the custom version of the Rust standard
libraries is to perform the following steps:

1. Clone the [`mir-json`](https://github.com/GaloisInc/mir-json) repo like so:

   :::{code-block} console
   $ git clone https://github.com/GaloisInc/mir-json
   $ cd mir-json
   :::

2. Follow the instructions laid out in the [`mir-json` installation
   instructions](https://github.com/GaloisInc/mir-json#installation-instructions)
   in order to install `mir-json`.

3. Run the `mir-json-translate-libs` utility:

   :::{code-block} console
   $ mir-json-translate-libs
   :::

   This will compile the custom versions of the Rust standard libraries using
   `mir-json`, placing the results under the `rlibs` subdirectory.

4. Finally, define a `SAW_RUST_LIBRARY_PATH` environment variable that points
   to the newly created `rlibs` subdirectory:

   :::{code-block} console
   $ export SAW_RUST_LIBRARY_PATH=<...>/mir-json/rlibs
   :::

An upcoming release of SAW will include these custom libraries pre-built, which
will greatly simplify the steps above. Either way, you will need to set the
`SAW_RUST_LIBRARY_PATH` environment variable to point to the location of the
custom libraries.

## A note about generics

The `id_u8` function above is likely not how most Rust programmers would define
the identity function. Instead, it would seem more natural to define it
generically, that is, by parameterizing the function by a type parameter:

:::{literalinclude} code/generics-take-1.rs
:language: rust
:::

If you compile this with `saw-rustc`, however, the resulting JSON file will
lack a definition for `id`! We can see this by using `jq`:

:::{code-block} console
$ saw-rustc generics-take-1.rs
<snip>
$ jq . generics-take-1.linked-mir.json
{
  "fns": [],
  "adts": [],
  "statics": [],
  "vtables": [],
  "traits": [],
  "intrinsics": [],
  "tys": [],
  "roots": []
}
:::

What is going on here? This is the result of an important design choice that
SAW makes: _SAW only supports verifying monomorphic functions_. To be more
precise, SAW's approach to symbolic simulation requires all of the code being
simulated to have fixed types without any type parameters.

In order to verify a function using generics in your Rust code, you must
provide a separate, monomorphic function that calls into the generic function.
For example, you can rewrite the example above like so:

:::{literalinclude} code/generics-take-2.rs
:language: rust
:::

If you compile this version with `saw-rustc`, you'll see:

:::{code-block} console
$ saw-rustc generics-take-2.rs
<snip>
note: Emitting MIR for generics_take_2/8b1bf337::id_u8

note: Emitting MIR for generics_take_2/8b1bf337::id::_instaddce72e1232152c[0]

linking 1 mir files into generics-take-2.linked-mir.json
<snip>
:::

This time, the resulting JSON file contains a definition for `id_u8`. The
reason that this works is because when `id_u8` calls `id`, the Rust compile
will generate a specialized version of `id` where `A` is instantiated with the
type `u8`. This specialized version of `id` is named
`id::_instaddce72e1232152c[0]` in the output above. (You don't have to remember
this name, thankfully!)

Although the resulting JSON file contains a definition for `id_u8`, it does
_not_ contain a definition for the generic `id` function. As a result, SAW will
only be able to verify the `id_u8` function from this file. If you are ever in
doubt about which functions are accessible for verification with SAW, you can
check this with `jq` like so:

:::{code-block} console
$ jq '.intrinsics | map(.name)' generics-take-2.linked-mir.json
[
  "generics_take_2/8b1bf337::id_u8",
  "generics_take_2/8b1bf337::id::_instaddce72e1232152c[0]"
]
:::

Here, "intrinsics" are monomorphic functions that are visible to SAW. Note that
`saw-rustc` will optimize away all definitions that are not accessible from one
of these intrinsic functions. This explains why the original program that only
defined a generic `id` function resulted in a definition-less JSON file, as
that program did not contain monomorphic functions (and therefore no
intrinsics).

Generally speaking, we prefer to verify functions that are defined directly in
the Rust source code, such as `id_u8`, as these functions' names are more
stable than the specialized versions of functions that the compiler generates,
such as `id::_instaddce72e1232152c[0]`. Do note that SAW is capable of
verifying both types of functions, however. (We will see an example of
verifying an autogenerated function in the Salsa20 case study later in this
tutorial.)

Proof scripts are more robust if we avoid direct mentions of compiler generated
names, such as `id::_instaddce72e1232152c[0]`.  To help with this, SAW provides
the command `mir_find_name : MIRModule -> String -> [MIRType] -> String`,
which may be used to lookup the compiler generated name in the intrinsics table
mentioned above.   For example, we could give a stable name to the compiler
generated name like this:

:::{code-block} sawscript
let id_inst8 = mir_find_name m "generics_take_2::id" [mir_u8]
:::


## Identifiers

When you compile a function named `id_u8`, `saw-rustc` will expand it to a much
longer name such as `first_example/abef32c5::id_u8`. This longer name is called
an _identifier_, and it provides a globally unique name for that function. In
the small examples we've seen up to this point, there hasn't been any risk of
name collisions, but you could imagine compiling this code alongside another
file (or crate) that also defines an `id_u8` function. If that happens, then it
is essential that we can tell apart all of the different `id_u8` functions, and
identifiers provide us the mechanism for doing so.

Let's take a closer look at what goes into an identifier. In general, an identifier
will look like the following:

:::{code-block}
<crate name>/<disambiguator>::<function path>
:::

`<crate name>` is the name of the crate in which the function is defined. All
of the examples we've seen up to this point have been defined in standalone
files, and as a result, the crate name has been the same as the file name, but
without the `.rs` extension and with all hyphens replaced with underscores
(e.g., `first-example.rs` is given the crate name `first_example`). In
`cargo`-based projects, the crate name will likely differ from the file name.

`<disambiguator>` is a hash of the crate and its dependencies. In extreme
cases, it is possible for two different crates to have identical crate names,
in which case the disambiguator must be used to distinguish between the two
crates. In the common case, however, most crate names will correspond to
exactly one disambiguator. (More on this in a bit.)

`<function path>` is the path to the function within the crate. Sometimes, this
is as simple as the function name itself. In other cases, a function path may
involve multiple _segments_, depending on the module hierarchy for the program
being verified. For instance, a `read` function located in
`core/src/ptr/mod.rs` will have the identifier:

:::{code-block}
core/<disambiguator>::ptr::read
:::

Where `core` is the crate name and `ptr::read` is the function path, which
has two segments `ptr` and `read`. There are also some special forms of
segments that appear for functions defined in certain language constructs.
For instance, if a function is defined in an `impl` block, then it will have
`{impl}` as one of its segments, e.g.,

:::{code-block}
core/<disambiguator>::ptr::const_ptr::{impl}::offset
:::

The most cumbersome part of writing an identifier is the disambiguator, as it
is extremely sensitive to changes in the code (not to mention hard to remember
and type). Luckily, the vast majority of crate names correspond to exactly one
disambiguator, and we can exploit this fact to abbreviate identifiers that live
in such crates. For instance, we can abbreviate this identifier:

:::{code-block}
core/<disambiguator>::ptr::read
:::

To simply:

:::{code-block}
core::ptr::read
:::

We will adopt the latter, shorter notation throughout the rest of the tutorial.
SAW also understands this shorthand, so we will also use this notation when
passing identifiers to SAW commands.
