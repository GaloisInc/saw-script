# Static items

Sometimes, Rust code makes use of [_static
items_](https://doc.rust-lang.org/reference/items/static-items.html), which are
definitions that are defined in a precise memory location for the entire
duration of the program. As such, static items can be thought of as a form of
global variables.

## Immutable static items

There are two kinds of static items in Rust: mutable static items (which have a
`mut` keyword) and immutable static items (which lack `mut`). Immutable static
items are much easier to deal with, so let's start by looking at an example of
a program that uses immutable static data:

:::{literalinclude} code/statics.rs
:lines: 1-5
:language: rust
:::

This function will return `ANSWER`, i.e., `42`. We can write a spec that says
as much:

:::{literalinclude} code/statics.saw
:lines: 3-7
:language: sawscript
:::

This works, but it is somewhat unsatisfying, as it requires hard-coding the
value of `ANSWER` into the spec. Ideally, we'd not have to think about the
precise implementation of static items like `ANSWER`. Fortunately, SAW makes
this possible by providing a `mir_static_initializer` function which computes
the initial value of a static item at the start of the program:

:::{code-block} console
sawscript> :type mir_static_initializer
String -> MIRValue
:::

In this case, `mir_static_initializer "statics::ANSWER"` is equivalent to
writing `mir_term {{ 42 : [32] }}`, so this spec is also valid:

:::{literalinclude} code/statics.saw
:lines: 12-16
:language: sawscript
:::

Like `mir_verify`, the `mir_static_initializer` function expects a full
identifier as an argument, so we must write `"statics::ANSWER"` instead of
just `"ANSWER"`.

At the MIR level, there is a unique reference to every static item. You can
obtain this reference by using the `mir_static` function:

:::{code-block} console
sawscript> :type mir_static
String -> MIRValue
:::

Here is one situation in which you would need to use a _reference_ to a static
item (which `mir_static` computes) rather than the _value_ of a static item
(which `mir_static_initializer` computes):

:::{literalinclude} code/statics.rs
:lines: 7-9
:language: rust
:::

A spec for this function would look like this:

:::{literalinclude} code/statics.saw
:lines: 21-25
:language: sawscript
:::

That's about all there is to say regarding immutable static items.

## Mutable static items

Mutable static items are a particularly tricky aspect of Rust. Including a
mutable static item in your program is tantamount to having mutable global
state that any function can access and modify. They are so tricky, in fact,
that Rust does not even allow you to use them unless you surround them in an
`unsafe` block:

:::{literalinclude} code/statics.rs
:lines: 11-15
:language: rust
:::

The `mir_static_initializer` and `mir_static` functions work with both immutable and
mutable static items, so we can write specs for mutable items using mostly the
same techniques as for writing specs for immutable items. We must be careful,
however, as SAW is pickier when it comes to specifying the initial values of
mutable static items. For example, here is a naïve attempt at porting the spec
for `answer_to_the_ultimate_question` over to its mutable static counterpart,
`mut_answer_to_the_ultimate_question`:

:::{literalinclude} code/statics-fail.saw
:lines: 3-7
:language: sawscript
:::

This looks plausible, but SAW will fail to verify it:

:::{code-block} console
[21:52:32.738] Verifying statics/28a97e47::mut_answer_to_the_ultimate_question[0] ...
[21:52:32.745] Simulating statics/28a97e47::mut_answer_to_the_ultimate_question[0] ...
...
Symbolic execution failed.
Abort due to assertion failure:
  statics.rs:14:14: 14:24: error: in statics/28a97e47::mut_answer_to_the_ultimate_question[0]
  attempted to read empty mux tree
:::

Oh no! Recall that we have seen this "`attempted to read empty mux tree`" error
message once before when discussing reference types. This error arose when we
attempted to read from uninitialized memory from a reference value. The same
situation applies here. A static item is backed by a reference, and SAW
deliberately does _not_ initialize the memory that a mutable static reference
points to upon program startup. Since we did not initialize `MUT_ANSWER`'s
reference value in the preconditions of the spec, SAW crashes at simulation
time when it attempts to read from the uninitialized memory.

The solution to this problem is to perform this initialization explicitly using
`mir_points_to` in the preconditions of the spec. For example, this is a valid
spec:

:::{literalinclude} code/statics.saw
:lines: 30-38
:language: sawscript
:::

We don't necessarily have to use `mir_static_initializer` as the starting value
for `MUT_ANSWER`, however. This spec, which uses `27` as the starting value, is
equally valid:

:::{literalinclude} code/statics.saw
:lines: 43-50
:language: sawscript
:::

At this point, you are likely wondering: why do we need to explicitly
initialize mutable static references but not immutable static references? After
all, when we wrote a spec for `answer_to_the_ultimate_question` earlier, we
managed to get away with not initializing the reference for `ANSWER` (which is
an immutable static item). The difference is that the value of a mutable static
item can change over the course of a program, and SAW requires that you be very
careful in specifying what a mutable static value is at the start of a
function. For example, consider a slightly extended version of the earlier Rust
code we saw:

:::{literalinclude} code/statics.rs
:lines: 11-22
:language: rust
:::

Suppose someone were to ask you "what value does
`mut_answer_to_the_ultimate_question` return?" This is not a straightforward
question to answer, as the value that it returns depends on the surrounding
context. If you were to call `mut_answer_to_the_ultimate_question` right as the
program started, it would return `42`. If you were to call
`mut_answer_to_the_ultimate_question` as part of the implementation of
`alternate_universe`, however, then it would return `27`! This is an inherent
danger of using mutable static items, as they can be modified at any time by
any function. For this reason, SAW requires you to be explicit about what the
initial values of mutable static items should be.

### Mutable static items and compositional overrides

In the "Overrides and mutable references" section, we discussed the potential
pitfalls of using mutable references in compositional overrides. Mutable static
items are also mutable values that are backed by references, and as such, they
are also subject to the same pitfalls. Let's see an example of this:

:::{literalinclude} code/statics-compositional.rs
:lines: 1-12
:language: rust
:::

The setup is almost the same, except that instead of passing a mutable
reference as an argument to `side_effect`, we instead declare a mutable static
item `A` that is shared between `side_effect` and `foo`. We could potentially
write SAW specs for `side_effect` and `foo` like these:

:::{literalinclude} code/statics-compositional-fail.saw
:lines: 3-18
:language: sawscript
:::

Note that we have once again underspecified the behavior of `side_effect`, as
we do not say what `A`'s value should be in the postconditions of
`side_effect_spec`. Similarly, `foo_spec` is wrong, as it should return `0`
rather than the initial value of `A`. By similar reasoning as before, we run
the risk that using `side_effect_ov` could lead us to prove something
incorrect. Thankfully, SAW can also catch this sort of mistake:

:::{code-block} console
[15:46:38.525] Verifying statics_compositional/16fea9c0::side_effect[0] ...
[15:46:38.533] Simulating statics_compositional/16fea9c0::side_effect[0] ...
[15:46:38.533] Checking proof obligations statics_compositional/16fea9c0::side_effect[0] ...
[15:46:38.533] Proof succeeded! statics_compositional/16fea9c0::side_effect[0]
[15:46:38.533] Verifying statics_compositional/16fea9c0::foo[0] ...
[15:46:38.542] Simulating statics_compositional/16fea9c0::foo[0] ...
[15:46:38.542] Matching 1 overrides of  statics_compositional/16fea9c0::side_effect[0] ...
[15:46:38.542] Branching on 1 override variants of statics_compositional/16fea9c0::side_effect[0] ...
...
State of mutable static variable "statics_compositional/16fea9c0::A[0]" not described in postcondition
:::

To repair this proof, add a `mir_points_to` statement in the postconditions of
`side_effect_spec`:

:::{literalinclude} code/statics-compositional.saw
:lines: 5-11
:language: sawscript
:::

And then correct the behavior of `foo_spec`:

:::{literalinclude} code/statics-compositional.saw
:lines: 13-20
:language: sawscript
:::

Be warned that if your program declares any mutable static items, then any
compositional override _must_ state what the value of each mutable static item
is in its postconditions. This applies _even if the override does not directly
use the mutable static items_. For example, if we had declared a second mutable
static item alongside `A`:

:::{code-block} rust
static mut A: u32 = 42;
static mut B: u32 = 27;
:::

Then `side_effect_spec` would need an additional `mir_points_to` statement
involving `B` to satisfy this requirement. This requirement is somewhat
heavy-handed, but it is necessary in general to avoid unsoundness. Think
carefully before you use mutable static items!
