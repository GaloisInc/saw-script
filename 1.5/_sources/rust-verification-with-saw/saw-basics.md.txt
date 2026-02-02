# SAW basics

## A first SAW example

We now have the knowledge necessary to compile Rust code in a way that is
suitable for SAW. Let's put our skills to the test and verify something! We will
build on the example from above, which we will put into a file named
`saw-basics.rs`:

:::{literalinclude} code/saw-basics.rs
:language: rust
:::

Our goal is to verify the correctness of the `id_u8` function. However, it is
meaningless to talk about whether a function is correct without having a
_specification_ for how the function should behave. This is where SAW enters
the picture. SAW provides a scripting language named _SAWScript_ that allows
you to write a precise specification for describing a function's behavior. For
example, here is a specification that captures the intended behavior of
`id_u8`:

:::{literalinclude} code/saw-basics.saw
:lines: 1-5
:language: sawscript
:::

At a high level, this specification says that `id_u8` is a function that accepts
a single argument of type `u8`, and it returns its argument unchanged. Nothing
too surprising there, but this example illustrates many of the concepts that one
must use when working with SAW. Let's unpack what this is doing, line by line:

* In SAWScript, specifications are ordinary values that are defined with `let`.
  In this example, we are defining a specification named `id_u8_spec`.
* Specifications are defined using "`do`-notation". That is, they are assembled
  by writing `do { <stmt>; <stmt>; ...; <stmt>; }`, where each `<stmt>` is a
  statement that declares some property about the function being verified. A
  statement can optionally bind a variable that can be passed to later
  statements, which is accomplished by writing `<var> <- <stmt>`.
* The `x <- mir_fresh_var "x" mir_u8;` line declares that `x` is a fresh
  variable of type `u8` (represented by `mir_u8` in SAWScript) that has some
  unspecified value. In SAW parlance, we refer to these unspecified values as
  _symbolic_ values. SAW uses an SMT solver under the hood to reason about
  symbolic values.

  The `"x"` string indicates what name the variable `x` should have when sent
  to the underlying SMT solver. This is primarily meant as a debugging aid, and
  it is not required that the string match the name of the SAWScript variable.
  (For instance, you could just as well have passed `"x_smt"` or something
  else.)
* The `mir_execute_func [mir_term x];` line declares that the function should
  be invoked with `x` as the argument. For technical reasons, we pass
  `mir_term x` to `mir_execute_func` rather than just `x`; we will go over what
  `mir_term` does later in the tutorial.
* Finally, the `mir_return (mir_term x);` line declares that the function should
  return `x` once it has finished.

Now that we have a specification in hand, it's time to prove that `id_u8`
actually adheres to the spec. To do so, we need to load the MIR JSON version of
`id_u8` into SAW, which is done with the `mir_load_module` command:

:::{literalinclude} code/saw-basics.saw
:lines: 7
:language: sawscript
:::

This `m` variable contains the definition of `id_u8`, as well as the other code
defined in the program. We can then pass `m` to the `mir_verify` command, which
actually verifies that `id_u8` behaves according to `id_u8_spec`:

:::{literalinclude} code/saw-basics.saw
:lines: 9
:language: sawscript
:::

Here is what is going on in this command:

* The `m` and `"saw_basics::id_u8"` arguments instruct SAW to verify the
  `id_u8` function located in the `saw_basics` crate defined in `m`. Note that
  we are using the shorthand identifier notation here, so we are allowed to omit
  the disambiguator for the `saw_basics` crate.
* The `[]` argument indicates that we will not provide any function overrides to
  use when SAW simulates the `id_u8` function. (We will go over how overrides
  work later in the tutorial.)
* The `false` argument indicates that SAW should not use path satisfiability
  checking when analyzing the function. Path satisfiability checking is an
  advanced SAW feature that we will not be making use of in this tutorial, so we
  will always use `false` here.
* The `id_u8_spec` argument indicates that `id_u8` should be checked against the
  specification defined by `id_u8_spec`.
* The `z3` argument indicates that SAW should use the Z3 SMT solver to solve
  any proof goals that are generated during verification. SAW also supports
  other SMT solvers, although we will mostly use Z3 in this tutorial.

Putting this all together, our complete `saw-basics.saw` file is:

:::{literalinclude} code/saw-basics.saw
:language: sawscript
:::

Now that everything is in place, we can check this proof like so:

:::{code-block} console
$ saw saw-basics.saw



[16:14:07.006] Loading file "saw-basics.saw"
[16:14:07.009] Verifying saw_basics/f77ebf43::id_u8[0] ...
[16:14:07.017] Simulating saw_basics/f77ebf43::id_u8[0] ...
[16:14:07.017] Checking proof obligations saw_basics/f77ebf43::id_u8[0] ...
[16:14:07.017] Proof succeeded! saw_basics/f77ebf43::id_u8[0]
:::

Tada! SAW was successfully able to prove that `id_u8` adheres to its spec.

## Cryptol

The spec in the previous section is nice and simple. It's also not very
interesting, as it's fairly obvious at a glance that `id_u8`'s implementation
is correct. Most of the time, we want to verify more complicated functions
where the correspondence between the specification and the implementation is
not always so clear.

For example, consider this function, which multiplies a number by two:

:::{literalinclude} code/times-two.rs
:lines: 1-3
:language: rust
:::

The straightforward way to implement this function would be to return `2 * x`,
but the author of this function _really_ cared about performance. As such, the
author applied a micro-optimization that computes the multiplication with a
single left-shift (`<<`). This is the sort of scenario where we are pretty sure
that the optimized version of the code is equivalent to the original version,
but it would be nice for SAW to check this.

Let's write a specification for the `times_two` function:

:::{literalinclude} code/times-two.saw
:lines: 1-5
:language: sawscript
:::

This spec introduces code delimited by double curly braces `{{ ... }}`, which
is a piece of syntax that we haven't seen before. The code in between the curly
braces is written in [Cryptol](http://cryptol.net/documentation.html), a
language designed for writing high-level specifications of various algorithms.
Cryptol supports most arithmetic operations, so `2 * x` works exactly as you
would expect. Also note that the `x` variable was originally bound in the
SAWScript language, but it is possible to embed `x` into the Cryptol language
by referencing `x` within the curly braces. (We'll say more about how this
embedding works later.)

`{{ 2 * x }}` takes the Cryptol expression `2 * x` and lifts it to a SAW
expression. As such, this SAW spec declares that the function takes a single
`u32`-typed argument `x` and returns `2 * x`. We could have also wrote the
specification to declare that the function returns `x << 1`, but that would
have defeated the point of this exercise: we specifically want to check that
the function against a spec that is as simple and readable as possible.

Our full SAW file is:

:::{literalinclude} code/times-two.saw
:lines: 1-9
:language: sawscript
:::

Which we can verify is correct like so:

:::{code-block} console
$ saw times-two.saw



[17:51:35.469] Loading file "times-two.saw"
[17:51:35.497] Verifying times_two/6f4e41af::times_two[0] ...
[17:51:35.512] Simulating times_two/6f4e41af::times_two[0] ...
[17:51:35.513] Checking proof obligations times_two/6f4e41af::times_two[0] ...
[17:51:35.527] Proof succeeded! times_two/6f4e41af::times_two[0]
:::

Nice! Even though the `times_two` function does not literally return `2 * x`,
SAW is able to confirm that the function behaves as if it were implemented that
way.

## `Term`s and other types

Now that we know how Cryptol can be used within SAW, we can go back and explain
what the `mir_term` function does. It is helpful to examine the type of
`mir_term` by using SAW's interactive mode. To do so, run the `saw` binary
without any other arguments:

:::{code-block} console
$ saw
:::

Then run `:type mir_term`:

:::{code-block} console
sawscript> :type mir_term
Term -> MIRValue
:::

Here, we see that `mir_term` accepts a `Term` as an argument and returns a
`MIRValue`. In this context, the `Term` type represents a Cryptol value, and
the `MIRValue` type represents SAW-related MIR values. `Term`s can be thought
of as a subset of `MIRValue`s, and the `mir_term` function is used to promote a
`Term` to a `MIRValue`.

Most other MIR-related commands work over `MIRValue`s, as can be seen with
SAW's `:type` command:

:::{code-block} console
sawscript> :type mir_execute_func
[MIRValue] -> MIRSetup ()
sawscript> :type mir_return
MIRValue -> MIRSetup ()
:::

Note that `MIRSetup` is the type of statements in a MIR specification, and two
`MIRSetup`-typed commands can be chained together by using `do`-notation.
Writing `MIRSetup ()` means that the statement does not return anything
interesting, and the use of `()` here is very much analogous to how `()` is
used in Rust. There are other `MIRSetup`-typed commands that _do_ return
something interesting, as is the case with `mir_fresh_var`:

:::{code-block} console
sawscript> :type mir_fresh_var
String -> MIRType -> MIRSetup Term
:::

This command returns a `MIRSetup Term`, which means that when you write `x <-
mir_fresh_var ... ...` in a MIR specification, then `x` will be bound at type
`Term`.

Values of type `Term` have the property that they can be embedded into Cryptol
expression that are enclosed in double curly braces `{{ ... }}`. This is why
our earlier `{{ 2 * x }}` example works, as `x` is of type `Term`.

## Preconditions and postconditions

As a sanity check, let's write a naïve version of `times_two` that explicitly
returns `2 * x`:

:::{literalinclude} code/times-two.rs
:lines: 5-7
:language: rust
:::

It seems like we should be able to verify this `times_two_ref` function using
the same spec that we used for `times_two`:

:::{literalinclude} code/times-two-ref-fail.saw
:lines: 9
:language: sawscript
:::

Somewhat surprisingly, SAW fails to verify this function:

:::{code-block} console
$ saw times-two-ref-fail.saw



[18:58:22.578] Loading file "times-two-ref-fail.saw"
[18:58:22.608] Verifying times_two/56182919::times_two_ref[0] ...
[18:58:22.621] Simulating times_two/56182919::times_two_ref[0] ...
[18:58:22.622] Checking proof obligations times_two/56182919::times_two_ref[0] ...
[18:58:22.640] Subgoal failed: times_two/56182919::times_two_ref[0] attempt to compute `const 2_u32 * move _2`, which would overflow
[18:58:22.640] SolverStats {solverStatsSolvers = fromList ["SBV->Z3"], solverStatsGoalSize = 375}
[18:58:22.640] ----------Counterexample----------
[18:58:22.640]   x: 2147483648
[18:58:22.640] Stack trace:
"mir_verify" (times-two-ref-fail.saw:11:1-11:11)
Proof failed.
:::

The "`which would overflow`" portion of the error message suggests what went
wrong. When a Rust program is compiled with debug settings (which is the
default for `rustc` and `saw-rustc`), arithmetic operations such as
multiplication will check if the result of the operation can fit in the
requested number of bits. If not, the program will raise an error.

In this case, we must make the result of multiplication fit in a `u32`, which
can represent values in the range `0` to `2^^32 - 1` (where `^^` is Cryptol's
exponentiation operator). But it is possible to take a number in this range,
multiply it by two, and have the result fall outside of the range. In fact, SAW
gives us a counterexample with exactly this number: `2147483648`, which can
also be written as `2^^31`. Multiplying this by two yields `2^^32`, which is
just outside of the range of values expressible with `u32`. SAW's duties
include checking that a function cannot fail at runtime, so this function falls
afoul of that check.

Note that we didn't have this problem with the original definition of
`times_two` because the semantics of `<<` are such that if the result is too
large to fit in the requested type, then the result will _overflow_, i.e., wrap
back around to zero and count up. This means that `(2^^31) << 1` evaluates to
`0` rather than raising an error. Cryptol's multiplication operation also
performs integer overflow (unlike Rust in debug settings), which is why we
didn't notice any overflow-related issues when verifying `times_two`.

There are two possible ways that we can repair this. One way is to rewrite
`times_two_ref` to use Rust's
[`wrapping_mul`](https://doc.rust-lang.org/std/primitive.u32.html#method.wrapping_mul)
function, a variant of multiplication that always uses integer overflow.  This
work around the issue, but it is a bit more verbose.

The other way is to make our spec more precise such that we only verify
`times_two_ref` for particular inputs. Although `times_two_ref` will run into
overflow-related issues when the argument is `2^^31` or greater, it is
perfectly fine for inputs smaller than `2^^31`. We can encode such an
assumption in SAW by adding a _precondition_. To do so, we write a slightly
modified version of `times_two_spec`:

:::{literalinclude} code/times-two.saw
:lines: 11-16
:language: sawscript
:::

The most notable change is the `mir_precond {{ x < 2^^31 }};` line.
`mir_precond` (where "`precond`" is short for "precondition") is a command that
takes a `Term` argument that contains a boolean predicate, such as `{{ x <
2^^31 }}`. Declaring a precondition requires that this predicate must hold
during verification, and any values of `x` that do not satisfy this predicate
are not considered.

By doing this, we have limited the range of the function from `0` to `2^^31 -
1`, which is exactly the range of values for which `times_two_ref` is well
defined. SAW will confirm this if we run it:

:::{literalinclude} code/times-two.saw
:lines: 18
:language: sawscript
:::

:::{code-block} console
[19:23:53.480] Verifying times_two/56182919::times_two_ref[0] ...
[19:23:53.496] Simulating times_two/56182919::times_two_ref[0] ...
[19:23:53.497] Checking proof obligations times_two/56182919::times_two_ref[0] ...
[19:23:53.531] Proof succeeded! times_two/56182919::times_two_ref[0]
:::

We can add as many preconditions to a spec as we see fit. For instance, if we
only want to verify `times_two_ref` for positive integers, we could add an
additional assumption:

:::{literalinclude} code/times-two.saw
:lines: 20-26
:language: sawscript
:::

In addition to preconditions, SAW also supports postconditions. Whereas
preconditions represent conditions that must hold _before_ invoking a function,
postconditions represent conditions that must hold _after_ invoking a function.
We have already seen one type of postcondition in the form of the `mir_return`
command, which imposes a postcondition on what the return value must be equal
to.

We can introduce additional postconditions with the `mir_postcond` command.
For example, if we call `times_two_ref` with a positive argument, then it
should be the case that the return value should be strictly greater than the
argument value. We can check for this using `mir_postcond` like so:

:::{literalinclude} code/times-two.saw
:lines: 30-37
:language: sawscript
:::

An additional convenience that SAW offers is the `mir_assert` command.
`mir_assert` has the same type as `mir_precond` and `mir_postcond`, but
`mir_assert` can be used to declare both preconditions _and_ postconditions.
The difference is where `mir_assert` appears in a specification. If
`mir_assert` is used before the call to `mir_execute_func`, then it declares a
precondition. If `mir_assert` is used after the call to `mir_execute_func`,
then it declares a postcondition.

For example, we can rewrite `times_two_ref_positive_postcond_spec` to use
`mir_assert`s like so:

:::{literalinclude} code/times-two.saw
:lines: 41-48
:language: sawscript
:::

The choice of whether to use `mir_precond`/`mir_postcond` versus `mir_assert` is
mostly a matter personal taste.
