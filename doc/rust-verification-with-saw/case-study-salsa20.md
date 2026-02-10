# Case study: Salsa20

If you've made it this far into the tutorial, congrats! You've now been exposed
to all of the SAW fundamentals that you need to verify Rust code found in the
wild. Of course, talking about verifying real-world code is one thing, but
actually _doing_ the verification is another thing entirely. Making the jump
from the small examples to "industrial-strength" code can be intimidating.

To make this jump somewhat less frightening, the last part of this tutorial
will consist of a case study in using SAW to verify a non-trivial piece of Rust
code. In particular, we will be looking at a Rust implementation of the
[Salsa20](https://en.wikipedia.org/wiki/Salsa20) stream cipher. We do not
assume any prior expertise in cryptography or stream ciphers in this tutorial,
so don't worry if you are not familiar with Salsa20.

More than anything, this case study is meant to emphasize that verification is
an iterative process. It's not uncommon to try something with SAW and encounter
an error message. That's OK! We will explain what can go wrong when verifying
Salsa20 and how to recover from these mistakes. Later, if you encounter similar
issues when verifying your own code with SAW, the experience you have developed
when developing these proofs can inform you of possible ways to fix the issues.

## The `salsa20` crate

The code for this Salsa20 implementation we will be verifying can be found
under the
[`code/salsa20`](https://github.com/GaloisInc/saw-script/tree/master/doc/rust-tutorial/code/salsa20)
subdirectory. This code is adapted from version 0.3.0 of the `salsa20` crate,
which is a part of the
[`stream-ciphers`](https://github.com/RustCrypto/stream-ciphers) project. The
code implements Salsa20 as well as variants such as HSalsa20 and XSalsa20, but
we will only be focusing on the original Salsa20 cipher in this tutorial.

The parts of the crate that are relevant for our needs are mostly contained in
the
[`src/core.rs`](https://github.com/GaloisInc/saw-script/tree/master/doc/rust-tutorial/code/salsa20/src/core.rs)
file, as well as some auxiliary definitions in the
[`src/rounds.rs`](https://github.com/GaloisInc/saw-script/tree/master/doc/rust-tutorial/code/salsa20/src/rounds.rs)
and
[`src/lib.rs`](https://github.com/GaloisInc/saw-script/tree/master/doc/rust-tutorial/code/salsa20/src/lib.rs)
files. You can take a look at these files if you'd like, but you don't need to
understand everything in them just yet. We will introduce the relevant parts of
the code in the tutorial as they come up.

## Salsa20 preliminaries

Salsa20 is a stream cipher, which is a cryptographic technique for encrypting
and decrypting messages. A stream cipher encrypts a message by combining it
with a _keystream_ to produce a ciphertext (the encrypted message). Moreover,
the same keystream can then be combined with the ciphertext to decrypt it back
into the original message.

The original author of Salsa20 has published a specification for Salsa20
[here](https://cr.yp.to/snuffle/spec.pdf). This is a great starting point for a
formal verification project, as this gives us a high-level description of
Salsa20's behavior that will guide us in proving the functional correctness of
the `salsa20` crate. When we say that `salsa20` is functionally correct, we
really mean "proven correct with respect to the Salsa20 specification".

The first step in our project would be to port the Salsa20 spec to Cryptol
code, as we will need to use this code when writing SAW proofs. The process of
transcribing an English-language specification to executable Cryptol code is
interesting in its own right, but it is not the primary focus of this tutorial.
As such, we will save you some time by providing a pre-baked Cryptol
implementation of the Salsa20 spec
[here](https://github.com/GaloisInc/saw-script/blob/master/doc/rust-tutorial/code/salsa20/Salsa20.cry).
(This implementation is
[adapted](https://github.com/GaloisInc/cryptol-specs/blob/1366ccf71db9dca58b16ff04ca7d960a4fe20e34/Primitive/Symmetric/Cipher/Stream/Salsa20.cry)
from the [`cryptol-specs`](https://github.com/GaloisInc/cryptol-specs) repo.)

Writing the Cryptol version of the spec is only half the battle, however. We
still have to prove that the Rust implementation in the `salsa20` crate adheres
to the behavior prescribed by the spec, which is where SAW enters the picture.
As we will see shortly, the code in `salsa20` is not a direct port of the
pseudocode shown in the Salsa20 spec, as it is somewhat more low-level. SAW's
role is to provide us assurance that the behavior of the low-level Rust code
and the high-level Cryptol code coincide.

## A note about cryptographic security

As noted in the previous section, our goal is to prove that the behavior of
`salsa20` functions is functionally correct. This property should _not_ be
confused with cryptographic security. While functional correctness is an
important aspect of cryptographic security, a full cryptographic security audit
would encompass additional properties such as whether the code runs in constant
time on modern CPUs. As such, the SAW proofs we will write would not constitute
a full security audit (and indeed, the [`salsa20`
`README`](https://github.com/GaloisInc/saw-script/tree/master/doc/rust-tutorial/code/salsa20/README.md)
states that the crate has never received such an audit).

## An overview of the `salsa20` code

Before diving into proofs, it will be helpful to have a basic understanding of
the functions and data types used in the `salsa20` crate. Most of the
interesting code lives in
[`src/core.rs`](https://github.com/GaloisInc/saw-script/tree/master/doc/rust-tutorial/code/salsa20/src/core.rs).
At the top of this file, we have the `Core` struct:

:::{literalinclude} code/salsa20/src/core.rs
:lines: 8-14
:language: rust
:::

Let's walk through this:

* The `state` field is an array that is `STATE_WORDS` elements long, where
  `STATE_WORDS` is a commonly used alias for `16`:

  :::{literalinclude} code/salsa20/src/lib.rs
  :lines: 88-89
  :language: rust
  :::

* The `rounds` field is of type `PhantomData<R>`. If you haven't seen it
  before,
  [`PhantomData<R>`](https://doc.rust-lang.org/std/marker/struct.PhantomData.html)
  is a special type that tells the Rust compiler to pretend as though the
  struct is storing something of type `R`, even though a `PhantomData` value
  will not take up any space at runtime.

The reason that `Core` needs a `PhantomData<R>` field is because `R`
implements the `Rounds` trait:

:::{literalinclude} code/salsa20/src/rounds.rs
:lines: 1-5
:language: rust
:::

A core operation in Salsa20 is hashing its input through a series of
_rounds_. The `COUNT` constant indicates how many rounds should be performed.
The Salsa20 spec assumes 20 rounds:

:::{literalinclude} code/salsa20/src/rounds.rs
:lines: 23-29
:language: rust
:::

However, there are also reduced-round variants that perform 8 and 12 rounds,
respectively:

:::{literalinclude} code/salsa20/src/rounds.rs
:lines: 7-21
:language: rust
:::

Each number of rounds has a corresponding struct whose names begins with the
letter `R`. For instance, a `Core<R20>` value represents a 20-round Salsa20
cipher. Here is the typical use case for a `Core` value:

* A `Core` value is created using the `new` function:

  :::{literalinclude} code/salsa20/src/core.rs
  :lines: 18
  :language: rust
  :::

  We'll omit the implementation for now. This function takes a secret `Key`
  value and a unique `Nonce` value and uses them to produce the initial `state`
  in the `Core` value.

* After creating a `Core` value, the `counter_setup` and `rounds` functions are
  used to produce the Salsa20 keystream:

  :::{literalinclude} code/salsa20/src/core.rs
  :lines: 83
  :language: rust
  :::

  :::{literalinclude} code/salsa20/src/core.rs
  :lines: 90
  :language: rust
  :::

  We'll have more to say about these functions later.

* The _pièce de résistance_ is the `apply_keystream` function. This takes a
  newly created `Core` value, produces its keystream, and applies it to a
  message to produce the `output`:

  :::{literalinclude} code/salsa20/src/core.rs
  :lines: 68
  :language: rust
  :::

Our ultimate goal is to verify the `apply_keystream` function, which is the
Rust equivalent of the Salsa20 encryption function described in the spec.

## Building `salsa20`

The next step is to build the `salsa20` crate. Unlike the examples we have seen
up to this point, which have been self-contained Rust files, `salsa20` is a
`cargo`-based project. As such, we will need to build it using `cargo
saw-build`, an extension to the `cargo` package manager that integrates with
`mir-json`. Before you proceed, make sure that you have defined the
`SAW_RUST_LIBRARY_PATH` environment variable as described in [this
section](#saw-rust-lib-path-env-var).

To build the `salsa20` crate, perform the following steps:

:::{code-block} console
$ cd code/salsa20/
$ cargo saw-build
:::

Near the end of the build output, you will see a line that looks like this:

:::{code-block} console
linking 9 mir files into <...>/saw-script/doc/rust-tutorial/code/salsa20/target/x86_64-unknown-linux-gnu/debug/deps/salsa20-dd0d90f28492b9cb.linked-mir.json
:::

This is the location of the MIR JSON file that we will need to provide to SAW.
(When we tried it, the hash in the file name was `dd0d90f28492b9cb`, but it
could very well be different on your machine.) Due to how `cargo` works, the
location of this file is in a rather verbose, hard-to-remember location. For
this reason, we recommend copying this file to a different path, e.g.,

:::{code-block} console
$ cp <...>/saw-script/doc/rust-tutorial/code/salsa20/target/x86_64-unknown-linux-gnu/debug/deps/salsa20-dd0d90f28492b9cb.linked-mir.json code/salsa20/salsa20.linked-mir.json
:::

As a safeguard, we have also checked in a compressed version of this MIR JSON
file as
[`code/salsa20/salsa/salsa20.linked-mir.json.gz`](https://github.com/GaloisInc/saw-script/tree/master/doc/rust-verification-with-saw/code/salsa20/salsa20.linked-mir.json.gz).
In a pinch, you can extract this archive to obtain a copy of the MIR JSON file,
which is approximately 4.6 megabytes when uncompressed.

## Getting started with SAW

Now that we've built the `salsa20` crate, it's time to start writing some
proofs! Let's start a new `code/salsa20/salsa20.saw` file and fill it in with
the usual preamble:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 1
:language: sawscript
:::

We are also going to need to make use of the Cryptol implementation of the
Salsa20 spec, which is defined in
[`code/salsa20/Salsa20.cry`](https://github.com/GaloisInc/saw-script/tree/master/doc/rust-tutorial/code/salsa20/Salsa20.cry).
SAW allows you to import standalone Cryptol `.cry` files by using the `import`
command:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 2
:language: sawscript
:::

As an aside, note that we have also checked in a
[`code/salsa20/salsa20-reference.saw`](https://github.com/GaloisInc/saw-script/tree/master/doc/rust-tutorial/code/salsa20/salsa20-reference.saw),
which contains a complete SAW file. We encourage you _not_ to look at this file
for now, since following along with the tutorial is meant to illustrate the
"a-ha moments" that one would have in the process of writing the proofs. If you
become stuck while following along and absolutely need a hint, however, then
this file can help you become unstuck.

## Verifying our first `salsa20` function

Now it's time to start verifying some `salsa20` code. But where do we start?
It's tempting to start with `apply_keystream`, which is our end goal. This is
likely going to be counter-productive, however, as `apply_keystream` is a
large function with several moving parts. Throwing SAW at it immediately is
likely to cause it to spin forever without making any discernible progress.

For this reason, we will instead take the approach of working from the
bottom-up. That is, we will first verify the functions that `apply_keystream`
transitively invokes, and then leverage compositional verification to verify a
proof of `apply_keystream` using overrides. This approach naturally breaks up
the problem into smaller pieces that are easier to understand in isolation.

If we look at the implementation of `apply_keystream`, we see that it invokes
the `round` function, which in turn invokes the `quarter_round` function:

:::{literalinclude} code/salsa20/src/core.rs
:lines: 122-142
:language: rust
:::

`quarter_round` is built on top of the standard library functions
[`wrapping_add`](https://doc.rust-lang.org/std/primitive.usize.html#method.wrapping_add)
and
[`rotate_left`](https://doc.rust-lang.org/std/primitive.usize.html#method.rotate_left),
so we have finally reached the bottom of the call stack. This makes
`quarter_round` a good choice for the first function to verify.

The implementation of the Rust `quarter_round` function is quite similar to the
Cryptol `quarterround` function in `Salsa20.cry`:

:::{literalinclude} code/salsa20/Salsa20.cry
:lines: 10-16
:language: cryptol
:::

The Cryptol `quarterround` function doesn't have anything like the `state`
argument in the Rust `quarter_round` function, but let's not fret about that
too much yet. Our SAW spec is going to involve `quarterround` _somehow_—we just
have to figure out how to make it fit.

Let's start filling out the SAW spec for `quarter_round`:

:::{literalinclude} code/salsa20/salsa20-quarter_round-fail1.saw
:lines: 4
:language: sawscript
:::

We are going to need some fresh variables for the `a`, `b`, `c`, and `d`
arguments:

:::{literalinclude} code/salsa20/salsa20-quarter_round-fail1.saw
:lines: 5-8
:language: sawscript
:::

We will also need to allocate a reference for the `state` argument. The
reference's underlying type is `STATE_WORDS` (`16`) elements long:

:::{literalinclude} code/salsa20/salsa20-quarter_round-fail1.saw
:lines: 9-11
:language: sawscript
:::

Finally, we will need to pass these arguments to the function:

:::{literalinclude} code/salsa20/salsa20-quarter_round-fail1.saw
:lines: 13-19
:language: sawscript
:::

With that, we have a spec for `quarter_round`! It's not very interesting just
yet, as we don't specify what `state_ref` should point to after the function
has returned. But that's fine for now. When developing a SAW proof, it can be
helpful to first write out the "skeleton" of a function spec that only contains
the call to `mir_execute_func`, without any additional preconditions or
postconditions. We can add those later after ensuring that the skeleton works
as expected.

Let's check our progress thus far by running this through SAW:

:::{code-block} console
$ saw salsa20.saw
...
[23:16:05.080] Type errors:
  salsa20.saw:12:39-12:68: Unbound variable: "STATE_WORDS" (salsa20.saw:12:49-12:60)

  salsa20/salsa20.saw:11:31-11:60: Unbound variable: "STATE_WORDS" (salsa20.saw:11:41-11:52)
:::

We've already run into some type errors. Not too surprising, considering this
was our first attempt. The error message contains that `STATE_WORDS` is
unbound. This makes sense if you think about it, as `STATE_WORDS` is defined in
the Rust code, but not in the SAW file itself. Let's fix that by adding this
line to `salsa20.saw`:

:::{literalinclude} code/salsa20/salsa20-quarter_round-fail2.saw
:lines: 4
:language: sawscript
:::

That change fixes the type errors in `quarter_round_spec`. Hooray! Let's press
on.

Next, we need to add a call to `mir_verify`. In order to do this, we need to
know what the full identifier for the `quarter_round` function is. Because it
is defined in the `salsa20` crate and in the `core.rs` file, so we would expect
the identifier to be named `salsa20::core::quarter_round`:

:::{literalinclude} code/salsa20/salsa20-quarter_round-fail2.saw
:lines: 23-24
:language: sawscript
:::

However, SAW disagrees:

:::{code-block} console
[00:22:56.970] Stack trace:
"mir_verify" (salsa20.saw:26:3-26:13)
Couldn't find MIR function named: salsa20::core::quarter_round
:::

Ugh. This is a consequence of how `mir-json` disambiguates identifiers. Because
there is a separate `core` crate in the Rust standard libraries, `mir-json`
uses "`core#1`", a distinct name, to refer to the `core.rs` file. You can see
this for yourself by digging around in the MIR JSON file, if you'd like. (In a
future version of SAW, one will be able to [look this name
up](https://github.com/GaloisInc/saw-script/issues/1980) more easily.)

Once we change the identifier:

:::{literalinclude} code/salsa20/salsa20-quarter_round-fail3.saw
:lines: 23-24
:language: sawscript
:::

We can run SAW once more. This time, SAW complains about a different thing:

:::{code-block} console
[01:00:19.697] Verifying salsa20/10e438b3::core#1[0]::quarter_round[0] ...
[01:00:19.714] Simulating salsa20/10e438b3::core#1[0]::quarter_round[0] ...
[01:00:19.717] Checking proof obligations salsa20/10e438b3::core#1[0]::quarter_round[0] ...
[01:00:19.739] Subgoal failed: salsa20/10e438b3::core#1[0]::quarter_round[0] index out of bounds: the length is move _10 but the index is _9
[01:00:19.739] SolverStats {solverStatsSolvers = fromList ["SBV->Z3"], solverStatsGoalSize = 53}
[01:00:19.739] ----------Counterexample----------
[01:00:19.739]   a: 2147483648
:::

Here, SAW complains that we have an `index out of bounds`. Recall that we are
indexing into the `state` array, which is of length 16, using the
`a`/`b`/`c`/`d` arguments. Each of these arguments are of type `usize`, and
because we are declaring these to be symbolic, it is quite possible for each
argument to be 16 or greater, which would cause the index into `state` to be
out of bounds.

In practice, however, the only values of `a`/`b`/`c`/`d` that we will use are
less than 16. We can express this fact as a precondition:

:::{literalinclude} code/salsa20/salsa20-quarter_round-fail4.saw
:lines: 11-14
:language: sawscript
:::

That is enough to finally get SAW to verify this very stripped-down version of
`quarter_round_spec`. Some good progress! But we aren't done yet, as we don't
yet say what happens to the value that `state` points to after the function
returns. This will be a requirement if we want to use `quarter_round_spec` in
compositional verification (and we do want this), so we should address this
shortly.

Recall that unlike the Rust `quarter_round` function, the Cryptol
`quarterround` function doesn't have a `state` argument. This is because the
Rust function does slightly more than what the Cryptol function does. The Rust
function will look up elements of the `state` array, use them to perform the
computations that the Cryptol function does, and then insert the new values
back into the `state` array. To put it another way: the Rust function can be
thought of as a wrapper around the Cryptol function that also performs an
in-place bulk update of the `state` array.

In Cryptol, one can look up elements of an array using the `(@@)` function,
and one can perform in-place array updates using the `updates` function.
This translates into a postcondition that looks like this:

:::{literalinclude} code/salsa20/salsa20-quarter_round-fail4.saw
:lines: 26-28
:language: sawscript
:::

What does SAW think of this? Somewhat surprisingly, SAW finds a counterexample:

:::{code-block} console
[01:43:30.065] Verifying salsa20/10e438b3::core#1[0]::quarter_round[0] ...
[01:43:30.078] Simulating salsa20/10e438b3::core#1[0]::quarter_round[0] ...
[01:43:30.084] Checking proof obligations salsa20/10e438b3::core#1[0]::quarter_round[0] ...
[01:43:30.801] Subgoal failed: salsa20/10e438b3::core#1[0]::quarter_round[0] Literal equality postcondition

[01:43:30.801] SolverStats {solverStatsSolvers = fromList ["SBV->Z3"], solverStatsGoalSize = 1999}
[01:43:30.802] ----------Counterexample----------
[01:43:30.802]   a: 13
[01:43:30.802]   b: 3
[01:43:30.802]   c: 0
[01:43:30.802]   d: 0
[01:43:30.802]   state: [3788509705, 0, 0, 3223325776, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1074561051, 0, 0]
:::

Note that in this counterexample, the values of `c` and `d` are the same. In
the Rust version of the function, each element in `state` is updated
sequentially, so if two of the array indices are the same, then the value that
was updated with the first index will later be overwritten by the value at the
later index. In the Cryptol version of the function, however, all of the
positions in the array are updated simultaneously. This implicitly assumes that
all of the array indices are disjoint from each other, an assumption that we
are not encoding into `quarter_round_spec`'s preconditions.

At this point, it can be helpful to observe _how_ the `quarter_round` function
is used in practice. The call sites are found in the `rounds` function:

:::{literalinclude} code/salsa20/src/core.rs
:lines: 92-102
:language: rust
:::

Here, we can see that the values of `a`/`b`/`c`/`d` will only ever be chosen
from a set of eight possible options. We can take advantage of this fact to
constrain the possible set of values for `a`/`b`/`c`/`d`. The latest iteration
of the `quarter_round_spec` is now:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 8-26
:language: sawscript
:::

Note that:

* The `indices` value is constrained (via a precondition) to be one of the set
  of values that is chosen in the `rounds` function. (Note that `\/` is the
  logical-or function in Cryptol.) Each of these are concrete values that are
  less than `STATE_WORDS` (`16`), so we no longer need a precondition stating
  ``a < `STATE_WORDS /\ ...``.

* Because we now reference `indices` in the preconditions, we have moved its
  definition up. (Previously, it was defined in the postconditions section.)

With this in place, will SAW verify `quarter_round_spec` now?

:::{code-block} console
[02:14:02.037] Verifying salsa20/10e438b3::core#1[0]::quarter_round[0] ...
[02:14:02.051] Simulating salsa20/10e438b3::core#1[0]::quarter_round[0] ...
[02:14:02.057] Checking proof obligations salsa20/10e438b3::core#1[0]::quarter_round[0] ...
[02:14:18.616] Proof succeeded! salsa20/10e438b3::core#1[0]::quarter_round[0]
:::

At long last, it succeeds. Hooray! SAW does have to think for a while, however,
as this proof takes about 17 seconds to complete. It would be unfortunate to
have to wait 17 seconds on every subsequent invocation of SAW, and since we
still have other functions to verify, this is a very real possibility. For this
reason, it can be helpful to temporarily turn this use of `mir_verify` into a
`mir_unsafe_assume_spec`:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 38-42
:language: sawscript
:::

Once we are done with the entire proof, we can come back and remove this use of
`mir_unsafe_assume_spec`, as we're only using it as a time-saving measure.

## Verifying the `rounds` function

Now that we've warmed up, let's try verifying the `rounds` function, which is
where `quarter_round` is invoked. Here is the full definition of `rounds`:

:::{literalinclude} code/salsa20/src/core.rs
:lines: 90-108
:language: rust
:::

First, `rounds` performs `COUNT` rounds on the `state` argument. After this, it
takes each element of `self.state` and adds it to the corresponding element in
`state`.

Linking back at the Salsa20 spec, we can see that the `rounds` function is
_almost_ an implementation of the Salsa20(x) hash function. The only notable
difference is that while the Salsa20(x) hash function converts the results to
little-endian form, the `rounds` function does not. `Salsa20.cry` implements
this part of the spec here:

:::{literalinclude} code/salsa20/Salsa20.cry
:lines: 139-147
:language: cryptol
:::

Where `Salsa20` is the hash function, and `Salsa20_rounds` is the part of the
hash function that excludes the little-endian conversions. In other words,
`Salsa20_rounds` precisely captures the behavior of the Rust `rounds` function.

One aspect of the `rounds` function that will make verifying it slightly
different from verifying `quarter_rounds` is that `rounds` is defined in an
`impl` block for the `Core` struct. This means that the `&mut self` argument in
`rounds` has the type `&mut Core<R>`. As such, we will have to look up the
`Core` ADT in SAW using `mir_find_adt`.

This raises another question, however: when looking up `Core<R>`, what type
should we use to instantiate `R`? As noted above, our choices are `R8`, `R12`,
and `R20`, depending on how many rounds you want. For now, we'll simply
hard-code it so that `R` is instantiated to be `R8`, but we will generalize
this a bit later.

Alright, enough chatter—time to start writing a proof. First, let's look up the
`R8` ADT. This is defined in the `salsa20` crate in the `rounds.rs` file, so
its identifier becomes `salsa20::rounds::R8`:

:::{literalinclude} code/salsa20/salsa20-rounds-take-1.saw
:lines: 44
:language: sawscript
:::

Next, we need to look up the `PhantomData<R8>` ADT, which is used in the
`rounds` field of the `Core<R8>` struct. This is defined in `core::marker`:

:::{literalinclude} code/salsa20/salsa20-rounds-take-1.saw
:lines: 45
:language: sawscript
:::

Finally, we must look up `Core<R8>` itself. Like `quarter_round`, the `Core`
struct is defined in `salsa20::core#1`:

:::{literalinclude} code/salsa20/salsa20-rounds-take-1.saw
:lines: 46
:language: sawscript
:::

Now that we have the necessary prerequisites, let's write a spec for the
`rounds` function. First, we need to allocate a reference for the `self`
argument:

:::{literalinclude} code/salsa20/salsa20-rounds-take-1.saw
:lines: 48-49
:language: sawscript
:::

Next, we need to create symbolic values for the fields of the `Core` struct,
which `self_ref` will point to. The `self.state` field will be a fresh array,
and the `self.rounds` field will be a simple, empty struct value:

:::{literalinclude} code/salsa20/salsa20-rounds-take-1.saw
:lines: 50-51
:language: sawscript
:::

Finally, putting all of the `self` values together:

:::{literalinclude} code/salsa20/salsa20-rounds-take-1.saw
:lines: 52-53
:language: sawscript
:::

Next, we need a `state` argument (not to be confused with the `self.state`
field in `Core`). This is handled much the same as it was in
`quarter_round_spec`:

:::{literalinclude} code/salsa20/salsa20-rounds-take-1.saw
:lines: 55-57
:language: sawscript
:::

Lastly, we cap it off with a call to `mir_execute_func`:

:::{literalinclude} code/salsa20/salsa20-rounds-take-1.saw
:lines: 59-60
:language: sawscript
:::

(Again, we're missing some postconditions describing what `self_ref` and
`state_ref` point to after the function returns, but we'll return to that in a
bit.)

If we run SAW at this point, we see that everything in `rounds_spec`
typechecks, so we're off to a good start. Let's keep going and add a
`mir_verify` call.

Here, we are faced with an interesting question: what is the identifier for
`rounds::<R8>`? The `rounds` function is defined using generics, so we can't
verify it directly—we must instead verify a particular instantiation of
`rounds`. At present, there isn't a good way to look up what the identifiers
for instantiations of generic functions are (there [will be in the
future](https://github.com/GaloisInc/saw-script/issues/1980)), but it turns out
that the identifier for `rounds::<R8>` is this:

:::{literalinclude} code/salsa20/salsa20-rounds-take-1.saw
:lines: 62-63
:language: sawscript
:::

Note that we are using `quarter_round_ov` as a compositional override. Once
again, SAW is happy with our work thus far:

:::{code-block} console
[03:12:35.990] Proof succeeded! salsa20/10e438b3::core#1[0]::{impl#0}[0]::rounds[0]::_inst6e4a2d7250998ef7[0]
:::

Nice. Now let's go back and fill in the missing postconditions in
`rounds_spec`. In particular, we must declare what happens to both `self_ref`
and `state_ref`. A closer examination of the code in the Rust `rounds` function
reveals that the `self` argument is never modified at all, so that part is
easy:

:::{literalinclude} code/salsa20/salsa20-rounds-take-2.saw
:lines: 61
:language: sawscript
:::

The `state` argument, on the other hand, is modified in-place. This time, our
job is made easier by the fact that `Salsa20_rounds` implements _exactly_ what
we need. Because we are instantiating `rounds` at type `R8`, we must explicitly
state that we are using 8 rounds:

:::{literalinclude} code/salsa20/salsa20-rounds-take-2.saw
:lines: 62
:language: sawscript
:::

Once again, SAW is happy with our work. We're on a roll!

Now let's address the fact that we are hard-coding everything to `R8`, which is
somewhat uncomfortable. We can make things better by allowing the user to
specify the number of rounds. The first thing that we will need to change is
the `r_adt` definition, which is responsible for looking up `R8`. We want to turn
this into a function that, depending on the user input, will look up `R8`,
`R12`, or `R20`:

:::{literalinclude} code/salsa20/salsa20-rounds-take-3.saw
:lines: 44
:language: sawscript
:::

Where `str_concat` is a SAW function for concatenating strings together:

:::{code-block} console
sawscript> :type str_concat
String -> String -> String
:::

We also want to parameterize `phantom_data_adt` and `core_adt`:

:::{literalinclude} code/salsa20/salsa20-rounds-take-3.saw
:lines: 45-46
:language: sawscript
:::

Next, we need to parameterize `rounds_spec` by the number of rounds. This will
require changes in both the preconditions and postconditions. On the
preconditions side, we must pass the number of rounds to the relevant
functions:

:::{literalinclude} code/salsa20/salsa20-rounds-take-3.saw
:lines: 48-54
:language: sawscript
:::

And on the postconditions side, we must pass the number of rounds to the
Cryptol `Salsa20_rounds` function:

:::{literalinclude} code/salsa20/salsa20-rounds-take-3.saw
:lines: 64-65
:language: sawscript
:::

Finally, we must adjust the call to `rounds_spec` in the context of
`mir_verify` so that we pick `8` as the number of rounds:

:::{literalinclude} code/salsa20/salsa20-rounds-take-3.saw
:lines: 67-68
:language: sawscript
:::

SAW is happy with this generalization. To demonstrate that we have generalized
things correctly, we can also verify the same function at `R20` instead of
`R8`:

:::{literalinclude} code/salsa20/salsa20-rounds-take-3.saw
:lines: 69-70
:language: sawscript
:::

The only things that we had to change were the identifier and the argument to
`rounds_spec`. Not bad!

## Verifying the `counter_setup` function

We're very nearly at the point of being able to verify `apply_keystream`.
Before we do, however, there is one more function that `apply_keystream` calls,
which we ought to verify first: `counter_setup`. Thankfully, the implementation
of `counter_setup` is short and sweet:

:::{literalinclude} code/salsa20/src/core.rs
:lines: 83-86
:language: rust
:::

This updates the elements of the `state` array at indices `8` and `9` with the
lower 32 bits and the upper 32 bits of the `counter` argument, respectively.
At a first glance, there doesn't appear to be any function in `Salsa20.cry`
that directly corresponds to what `counter_setup` does. This is a bit of a
head-scratcher, but the answer to this mystery will become more apparent as we
get further along in the proof.

For now, we should take matters into our own hands and write our own Cryptol
spec for `counter_setup`. To do this, we will create a new Cryptol file named
`Salsa20Extras.cry`, which imports from `Salsa20.cry`:

:::{literalinclude} code/salsa20/Salsa20Extras.cry
:lines: 1-3
:language: cryptol
:::

The Cryptol implementation of `counter_setup` will need arrays of length
`STATE_WORDS`, so we shall define `STATE_WORDS` first:

:::{literalinclude} code/salsa20/Salsa20Extras.cry
:lines: 5
:language: cryptol
:::

Note that we preceded this definition with the `type` keyword. In Cryptol,
sequence lengths are encoded at the type level, so if we want to use
`STATE_WORDS` at the type level, we must declare it as a `type`.

Finally, we can write a Cryptol version of `counter_setup` using our old friend
`updates` to perform a bulk sequence update:

:::{literalinclude} code/salsa20/Salsa20Extras.cry
:lines: 8-10
:language: cryptol
:::

Note that `counter` is a 64-bit word, but the elements of the `state` sequence
are 32-bit words. As a result, we have to explicitly truncate `counter` and
`counter >> 32` to 32-bit words by using the `drop` function, which drops the
first 32 bits from each word.

Returning to `salsa20.saw`, we must now make use of our new Cryptol file by
`import`ing it at the top:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 3
:language: sawscript
:::

With the `counter_setup` Cryptol implementation in scope, we can now write
a spec for the Rust `counter_setup` function. There's not too much to remark
on here, as the spec proves relatively straightforward to write:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 72-88
:language: sawscript
:::

We can now verify `counter_setup` against `counter_setup_spec` at lengths `8`
and `20`:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 90-93
:language: sawscript
:::

That wasn't so bad. It's a bit unsatisfying that we had to resort to writing a
Cryptol function not found in `Salsa20.cry`, but go along with this for now—it
will become apparent later why this needed to be done.

## Verifying the `apply_keystream` function (first attempt)

It's time. Now that we've verified `rounds` and `counter_setup`, it's time to
tackle the topmost function in the call stack: `apply_keystream`:

:::{literalinclude} code/salsa20/src/core.rs
:lines: 68-80
:language: rust
:::

There aren't _that_ many lines of code in this function, but there is still
quite a bit going on. Let's walk through `apply_keystream` in more detail:

1. The `output` argument represents the message to encrypt (or decrypt).
   `output` is a slice of bytes, so in principle, `output` can have an arbitrary
   length. That being said, the first line of `apply_keystream`'s implementation
   checks that `output`'s length is equal to `BLOCK_SIZE`:

   :::{literalinclude} code/salsa20/src/core.rs
   :lines: 69
   :language: rust
   :::

   Where `BLOCK_SIZE` is defined here:

   :::{literalinclude} code/salsa20/src/lib.rs
   :lines: 82-83
   :language: rust
   :::

   So in practice, `output` must have exactly 64 elements.

2. Next, `apply_keystream` invokes the `counter_setup` and `rounds` functions
   to set up the keystream (the local `state` variable).

3. Finally, `apply_keystream` combines the keystream with `output`. It does
   so by chunking `output` into a sequence of 4 bytes, and then it XOR's the
   value of each byte in-place with the corresponding byte from the keystream.
   This performs little-endian conversions as necessary.

The fact that we are XOR'ing bytes strongly suggests that this is an
implementation of the Salsa20 encryption function from the spec. There is an
important difference between how the Salsa20 spec defines the encryption
function versus how `apply_keystream` defines it, however. In the Salsa20 spec,
encryption is a function of a key, nonce, and a message. `apply_keystream`, on
the other hand, is a function of `self`'s internal state, a counter, and a
message. The two aren't _quite_ the same, which makes it somewhat tricky to
describe one in terms of the other.

`Salsa20.cry` defines a straightforward Cryptol port of the Salsa20 encryption
function from the spec, named `Salsa20_encrypt`. Because it takes a key and a
nonce as an argument, it's not immediately clear how we'd tie this back to
`apply_keystream`. But no matter: we can do what we did before and define our
own Cryptol version of `apply_keystream` in `Salsa20Extras.cry`:

:::{literalinclude} code/salsa20/Salsa20Extras.cry
:lines: 12-17
:language: cryptol
:::

This implementation builds on top of the Cryptol `counter_setup` and
`Salsa20_rounds` functions, which we used as the reference implementations for
the Rust `counter_setup` and `rounds` functions, respectively. We also make
sure to define a `BLOCK_SIZE` type alias at the top of the file:

:::{literalinclude} code/salsa20/Salsa20Extras.cry
:lines: 6
:language: cryptol
:::

Now let's write a SAW spec for `apply_keystream`. Once again, we will need to
reference `BLOCK_SIZE` when talking about the `output`-related parts of the
spec, so make sure to define `BLOCK_SIZE` at the top of the `.saw` file:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 6
:language: sawscript
:::

First, we need to declare all of our arguments, which proceeds as you would
expect:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 118-134
:language: sawscript
:::

What about the postconditions? We have two mutable references to contend with:
`self_ref` and `output_ref`. The postcondition for `self_ref` is fairly
straightforward: the only time it is ever modified is when `counter_setup` is
called. This means that after the `apply_keystream` function has returned,
`self_ref` will point to the results of calling the `counter_setup` Cryptol
function:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 136-138
:language: sawscript
:::

`output_ref` is where the interesting work happenings. After the Rust
`apply_keystream` function has returned, it will point to the results of
calling the Cryptol `apply_keystream` function that we just defined:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 139-140
:language: sawscript
:::

Finally, we can put this all together and verify `apply_keystream` against
`apply_keystream_spec` at lengths `8` and `20`:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 142-146
:language: sawscript
:::

SAW will successfully verify these. We've achieved victory... or have we?
Recall that we had to tailor the Cryptol `apply_keystream` function to
specifically match the behavior of the corresponding Rust code. This makes the
proof somewhat underwhelming, since the low-level implementation is nearly
identical to the high-level spec.

A more impressive proof would require linking `apply_keystream` to a Cryptol
function in the `Salsa20.cry` file, which was developed independently of the
Rust code. As we mentioned before, however, doing so will force us to reconcile
the differences in the sorts of arguments that each function takes, as
`apply_keystream` doesn't take a key or nonce argument. Time to think for a
bit.

## Verifying the `new_raw` function

At this point, we should ask ourselves: _why_ doesn't `apply_keystream` take a
key or nonce argument? The reason lies in the fact that the `salsa20` crate
implements Salsa20 in a stateful way. Specifically, the `Core` struct stores
internal state that is used to compute the keystream to apply when hashing. In
order to use this internal state, however, we must first initialize it. The
`new` function that is responsible for this initialization:

:::{literalinclude} code/salsa20/src/core.rs
:lines: 17-20
:language: rust
:::

Sure enough, this function takes a key and a nonce as an argument! This is a
critical point that we overlooked. When using the `salsa20` crate, you wouldn't
use the `apply_keystream` function in isolation. Instead, you would create an
initial `Core` value using `new`, and _then_ you would invoke
`apply_keystream`. The Salsa20 spec effectively combines both of these
operations in its encryption function, whereas the `salsa20` splits these two
operations into separate functions altogether.

Strictly speaking, we don't need to verify `new` in order to verify
`apply_keystream`, as the latter never invokes the former. Still, it will be a
useful exercise to verify `new`, as the insights we gain when doing so will
help us write a better version of `apply_keystream_spec`.

All that being said, we probably want to verify `new_raw` (a lower-level helper
function) rather than `new` itself. This is because the definitions of `Key`
and `Nonce` are somewhat involved. For instance, `Key` is defined as:

:::{literalinclude} code/salsa20/src/salsa.rs
:lines: 27
:language: rust
:::

[`GenericArray`](https://docs.rs/generic-array/latest/generic_array/struct.GenericArray.html)
is a somewhat complicated abstraction. Luckily, we don't really _need_ to deal
with it, since `new_raw` deals with simple array references rather than
`GenericArray`s:

:::{literalinclude} code/salsa20/src/core.rs
:lines: 22-23
:language: rust
:::

The full implementation of `new_raw` is rather long, so we won't inline the
whole thing here. At a high level, it initializes the `state` array of a `Core`
value by populating each element of the array with various things. Some
elements of the array are populated with `key`, some parts are populated with
`iv` (i.e., the nonce), and other parts are populated with an array named
`CONSTANTS`:

:::{literalinclude} code/salsa20/src/lib.rs
:lines: 91-92
:language: rust
:::

The comment about `"expand 32-byte k"` is a strong hint that `new_raw` is
implementing a portion of the Salsa20 expansion function from the spec. (No
really, the spec literally says to use the exact string `"expand 32-byte
k"`—look it up!) The `Salsa20.cry` Cryptol file has an implementation of this
portion of the expansion function, which is named `Salsa20_init`:

:::{literalinclude} code/salsa20/Salsa20.cry
:lines: 182-189
:language: cryptol
:::

Note that we were careful to say a _portion_ of the Salsa20 expansion function.
There is also a Cryptol implementation of the full expansion function, named
`Salsa20_expansion`:

:::{literalinclude} code/salsa20/Salsa20.cry
:lines: 179-180
:language: cryptol
:::

This calls `Salsa20_init` followed by `Salsa20`, the latter of which performs
hashing. Importantly, `new_raw` does _not_ do any hashing on its own, just
initialization. For this reason, we want to use `Salsa20_init` as the reference
implementation of `new_raw`, not `Salsa20_expansion`.

Alright, time to write a SAW spec. The first part of the spec is straightforward:

:::{literalinclude} code/salsa20/salsa20-new_raw-fail1.saw
:lines: 95-104
:language: sawscript
:::

As is usually the case, the postconditions are the tricky part. We know that
the behavior of `new_raw` will roughly coincide with the `Salsa20_init`
function, so let's try that first:

:::{literalinclude} code/salsa20/salsa20-new_raw-fail1.saw
:lines: 106-110
:language: sawscript
:::

If we attempt to verify this using `mir_verify`:

:::{literalinclude} code/salsa20/salsa20-new_raw-fail1.saw
:lines: 113-116
:language: sawscript
:::

SAW complains thusly:

:::{code-block} console
Cryptol error:
[error] at salsa20.saw:109:45--109:54:
  Type mismatch:
    Expected type: 16
    Inferred type: 8
    Context: [ERROR] _
    When checking type of 2nd tuple field
:::

Here, the 2nd tuple field is the `nonce_arr` in `Salsa20_init(key_arr,
nonce_arr)`. And sure enough, `Salsa20_init` expects the 2nd tuple field to be
a sequence of 16 elements, but `nonce_arr` only has 8 elements. Where do we get
the remaining 8 elements from?

The answer to this question can be found by looking at the implementation of
`new_raw` more closely. Let's start at this code:

:::{literalinclude} code/salsa20/src/core.rs
:lines: 35-36
:language: rust
:::

This will chunk up `iv` (the nonce) into two 4-byte chunks and copies them over
to the elements of `state` array at indices `6` and `7`. This is immediately
followed by two updates at indices `8` and `9`, which are updated to be `0`:

:::{literalinclude} code/salsa20/src/core.rs
:lines: 39-40
:language: rust
:::

If you take the two 4-bytes chunks of `iv` and put two 4-byte `0` values after
them, then you would have a total of 16 bytes. This suggests that the nonce
value that `Salsa20_init` expects is actually this:

:::{code-block} cryptol
nonce_arr # zero : [16][8]
:::

Where `zero : [8][8]` is a Cryptol expression that returns all zeroes, and
`(#)` is the Cryptol operator for concatenating two sequences together. Let's
update `new_raw_spec` to reflect this:

:::{literalinclude} code/salsa20/salsa20-new_raw-fail2.saw
:lines: 107
:language: sawscript
:::

This is closer to what we want, but not quite. SAW still complains:

:::{code-block} console
could not match specified value with actual value:
  ...
  type of actual value:    [u32; 16]
  type of specified value: [u8; 64]
:::

This is because `Salsa20_init` returns something of type `[64][8]`, which
corresponds to the Rust type `[u8; 64]`. `self.state`, on the other hand, is of
type `[u32; 16]`. These types are very close, as they both contain the same
number of bytes, but they are chunked up differently. Recall the code that
copies the nonce value over to `self.state`:

:::{literalinclude} code/salsa20/src/core.rs
:lines: 35-36
:language: rust
:::

In order to resolve the type differences between `iv` and `state`, this code
needed to explicitly convert `iv` to little-endian form using the
[`u32::from_le_bytes`](https://doc.rust-lang.org/std/primitive.u32.html#method.from_le_bytes)
function. There is a similar Cryptol function in `Salsa20.cry` named
`littleendian_state`:

:::{literalinclude} code/salsa20/Salsa20.cry
:lines: 131-132
:language: cryptol
:::

Note that `[64][8]` is the Cryptol equivalent of `[u8; 64]`, and `[16][32]` is
the Cryptol equivalent of `[u32; 16]`. As such, this is exactly the function
that we need to resolve the differences in types:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 107
:language: sawscript
:::

With that change, SAW is finally happy with `new_raw_spec` and successfully
verifies it.

There is an interesting connection between the `new_raw` and `counter_setup`
functions. Both functions perform in-place updates on `state` at indices `8`
and `9`. Whereas `new_raw` always sets these elements of `state` to `0`,
`counter_setup` will set them to the bits of the `counter` argument (after
converting `counter` to little-endian form). This means that if you invoke
`counter_setup` right after `new_raw`, then `counter_setup` would overwrite the
`0` values with the `counter` argument. In order words, it would be tantamount
to initializing `state` like so:

:::{code-block} cryptol
littleendian_state (Salsa20_init(key, nonce # littleendian_inverse counter))
:::

Where `littleendian_inverse` (a sibling of `littleendian_state`) converts a
`[64]` value to a `[8][8]` one. This pattern is a curious one...

## Verifying the `apply_keystream` function (second attempt)

Let's now return to the problem of linking `apply_keystream` up to
`Salsa20_encrypt`. In particular, let's take a closer look at the definition of
`Salsa20_encrypt` itself:

:::{literalinclude} code/salsa20/Salsa20.cry
:lines: 198-201
:language: cryptol
:::

Does anything about this definition strike you as interesting? Take a look at
the `v#(littleendian_inverse i)` part—we _just_ saw a use of
`littleendian_inverse` earlier in our discussion about initializing the
`state`! Moreover, `v` is the nonce argument, so it is becoming clearer that
`Salsa20_encrypt` is creating an initial state in much the same way that
`new_raw` is.

A related question: what is the `i` value? The answer is somewhat technical:
the Salsa20 encryption function is designed to work with messages with
differing numbers of bytes (up to `2^^70` bytes, to be exact). Each 8-byte
chunk in the message will be encrypted with a slightly difference nonce. For
instance, the first 8-byte chunk's nonce will have its lower 32 bits set to
`0`, the second 8-byte chunk's nonce will have its lower 32 bits set to `1`,
and so on. In general, the `i`th 8-byte chunk's nonce will have its lower 32
bits set to `i`, and this corresponds exactly to the `i` in the expression
`littleendian_inverse i`.

Note, however, that `apply_keystream` only ever uses a message that consists of
exactly eight 8-byte chunks. This means that `Salsa20_encrypt` will only ever
invoke `Salsa20_expansion` once with a nonce value where the lower 32 bits are
set to `0`. That is, it will perform encryption with an initial state derived
from:

:::{code-block} cryptol
Salsa20_init(k, v#(littleendian_inverse zero))
:::

Which can be further simplified to `Salsa20_init(k, v # zero)`. This is very
nearly what we want, as this gives us the behavior of the Rust `new_raw`
function. There's just one problem though: it doesn't take the behavior of
`counter_setup` into account. How do we go from `zero` to `littleendian_inverse
counter`?

While `Salsa20_encrypt` doesn't take counters into account at all, it is not
too difficult to generalize `Salsa20_encrypt` in this way. There is a variant
of `Salsa20_encrypt` in the same file named `Salsa20_encrypt_with_offset`,
where the offset argument `o` serves the same role that `counter` does in
`counter_setup`:

:::{literalinclude} code/salsa20/Salsa20.cry
:lines: 191-196
:language: cryptol
:::

(Observe that `Salsa20_encrypt(count, k, v, m)` is equivalent to
`Salsa20_encrypt_with_offset(count, k, v, 0, m)`.)

At long last, we have discovered the connection between `apply_keystream` and
the Salsa20 spec. If you assume that you invoke `new_raw` beforehand, then the
behavior of `apply_keystream` corresponds exactly to that of
`Salsa20_encrypt_with_offset`. This insight will inform us how to write an
alternative SAW spec for `apply_keystream`:

:::{literalinclude} code/salsa20/salsa20-apply_keystream_alt-fail1.saw
:lines: 147-158
:language: sawscript
:::

Observe the following differences between `apply_keystream_alt_spec` and our
earlier `apply_keystream_spec`:

1. In `apply_keystream_alt_spec`, we declare fresh `key` and `nonce` values,
   which weren't present at all in `apply_keystream_spec`.

2. In `apply_keystream_alt_spec`, we no longer make `self_state` a fresh,
   unconstrained value. Instead, we declare that it must be the result of
   calling `Salsa20_init` on the `key`, `nonce`, and `counter` values. This
   is the part that encodes the assumption that `new_raw` was invoked
   beforehand.

The parts of the spec relating to `output` remain unchanged:

:::{literalinclude} code/salsa20/salsa20-apply_keystream_alt-fail1.saw
:lines: 160-165
:language: sawscript
:::

The postconditions are slightly different in `apply_keystream_alt_spec`. While
the parts relating to `self_ref` remain unchanged, we now have `output_ref`
point to the results of calling `Salsa20_encrypt_with_offset`:

:::{literalinclude} code/salsa20/salsa20-apply_keystream_alt-fail1.saw
:lines: 167-170
:language: sawscript
:::

Tying this all together, we call `mir_verify`, making sure to use compositional
overrides involving `counter_setup` and `rounds`:

:::{literalinclude} code/salsa20/salsa20-apply_keystream_alt-fail1.saw
:lines: 173-176
:language: sawscript
:::

At long last, it is time to run SAW on this. When we do, we see this:

:::{code-block} console
[15:11:44.576] Checking proof obligations salsa20/10e438b3::core#1[0]::{impl#0}[0]::apply_keystream[0]::_inst6e4a2d7250998ef7[0] ...
:::

After this, SAW loops forever. Oh no! While somewhat disheartening, this is a
reality of SMT-based verification that we must content with. SMT solvers are
extremely powerful, but their performance can sometimes be unpredictable. The
task of verifying `apply_keystream_alt_spec` is _just_ complicated enough that
Z3 cannot immediately figure out that the proof is valid, so it resorts to much
slower algorithms to solve proof goals.

We could try waiting for Z3 to complete, but we'd be waiting for a long time.
It's not unheard of for SMT solvers to take many hours on especially hard
problems, but we don't have that many hours to spare. We should try a slightly
different approach instead.

When confronted with an infinite loop in SAW, there isn't a one-size-fits-all
solution that will cure the problem. Sometimes, it is worth stating your SAW
spec in a slightly different way such that the SMT solver can spot patterns
that it couldn't before. Other times, it can be useful to try and break the
problem up into smaller functions and use compositional verification to handle
the more complicated subfunctions. As we mentioned before, the performance of
SMT solvers is unpredictable, and it's not always obvious what the best
solution is.

In this example, however, the problem lies with Z3 itself. As it turns out,
Yices (a different SMT solver) _can_ spot the patterns needed to prove
`apply_keystream_alt_spec` immediately. Fortunately, SAW includes support for
both Z3 and Yices. In order to switch from Z3 to Yices, swap out the `z3` proof
script with `yices`:

:::{literalinclude} code/salsa20/salsa20-reference.saw
:lines: 173-176
:language: sawscript
:::

After doing this, SAW leverages Yices to solve the proof goals almost
immediately:

:::{code-block} console
[15:22:00.745] Proof succeeded! salsa20/10e438b3::core#1[0]::{impl#0}[0]::apply_keystream[0]::_instfa33e77d840484a0[0]
:::

And with that, we're finally done! You've successfully completed a non-trivial
SAW exercise in writing some interesting proofs. Give yourself a well-deserved
pat on the back.

The process of developing these proofs was bumpy at times, but that is to be
expected. You very rarely get a proof correct on the very first try, and when
SAW doesn't accept your proof, it is important to be able to figure out what
went wrong and how to fix it. This is a skill that takes some time to grow, but
with enough time and experience, you will be able to recognize common pitfalls.
This case study showed off some of these pitfalls, but there are likely others.
