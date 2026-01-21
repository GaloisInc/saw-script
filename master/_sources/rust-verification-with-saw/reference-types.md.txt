# Reference types

All of the examples we have seen up to this point involve simple integer types
such as `u8` and `u32`. While these are useful, Rust's type system features
much more than just integers. A key part of Rust's type system are its
reference types. For example, in this `read_ref` function:

:::{literalinclude} code/ref-basics.rs
:lines: 1-3
:language: rust
:::

The function reads the value that `r` (of type `&u32`) points to and returns
it. Writing SAW specifications involving references is somewhat trickier than
with other types of values because we must also specify what memory the
reference points to. SAW provides a special command for doing this called
`mir_alloc`:

:::{code-block} console
sawscript> :type mir_alloc
MIRType -> MIRSetup MIRValue
:::

`mir_alloc` will allocate a reference value with enough space to hold a value
of the given `MIRType`.  Unlike `mir_fresh_var`, `mir_alloc` returns a
`MIRValue` instead of a `Term`.  We mentioned before that `Term`s are only a
subset of `MIRValue`s, and this is one of the reasons why. Cryptol does not
have a notion of reference values, but `MIRValue`s do. As a result, you cannot
embed the result of a call to `mir_alloc` in a Cryptol expression.

`mir_alloc` must be used with some care. Here is a first, not-quite-correct
attempt at writing a spec for `read_ref` using `mir_alloc`:

:::{literalinclude} code/ref-basics-fail.saw
:lines: 1-9
:language: sawscript
:::

As the comment suggests, it's not entirely clear what this spec should return.
We can't return `r`, since `read_ref` returns something of type `u32`, not
`&u32`. On the other hand, we don't have any values of type `u32` lying around
that are obviously the right thing to use here. Nevertheless, it's not required
for a SAW spec to include a `mir_return` statement, so let's see what happens
if we verify this as-is:

:::{code-block} console
$ saw ref-basics-fail.saw



[20:13:27.224] Loading file "ref-basics-fail.saw"
[20:13:27.227] Verifying ref_basics/54ae7b63::read_ref[0] ...
[20:13:27.235] Simulating ref_basics/54ae7b63::read_ref[0] ...
[20:13:27.235] Stack trace:
"mir_verify" (ref-basics-fail.saw:11:1-11:11)
Symbolic execution failed.
Abort due to assertion failure:
  ref-basics.rs:2:5: 2:7: error: in ref_basics/54ae7b63::read_ref[0]
  attempted to read empty mux tree
:::

Clearly, SAW didn't like what we gave it. The reason this happens is although
we allocated memory for the reference `r`, we never told SAW what value should
live in that memory. When SAW simulated the `read_ref` function, it attempted
to dereference `r`, which pointed to uninitialized memory. This constitutes
an error in SAW, which is what this "`attempted to read empty mux tree`"
business is about.

SAW provides a `mir_points_to` command to declare what value a reference should
point to:

:::{code-block} console
sawscript> :type mir_points_to
MIRValue -> MIRValue -> MIRSetup ()
:::

Here, the first `MIRValue` argument represents a reference value, and the
second `MIRValue` argument represents the value that the reference should point
to. In our spec for `read_ref`, we can declare that the reference should point
to a symbolic `u32` value like so:

:::{literalinclude} code/ref-basics.saw
:lines: 1-7
:language: sawscript
:::

We have renamed `r` to `r_ref` in this revised spec to more easily distinguish
it from `r_val`, which is the value that `r_ref` is declared to point to using
`mir_points_to`. In this version of the spec, it is clear that we should return
`r_val` using `mir_return`, as `r_val` is exactly the value that will be
computed by dereferencing `r_ref`.

This pattern, where a call to `mir_alloc`/`mir_alloc_mut` to followed by a call
to `mir_points_to`, is common with function specs that involve references.
Later in the tutorial, we will see other examples of `mir_points_to` where the
reference argument does not come from `mir_alloc`/`mir_alloc_mut`.

The argument to `read_ref` is an immutable reference, so the implementation of
the function is not allowed to modify the memory that the argument points to.
Rust also features mutable references that do permit modifying the underlying
memory, as seen in this `swap` function:

:::{literalinclude} code/ref-basics.rs
:lines: 5-11
:language: rust
:::

A corresponding spec for `swap` is:

:::{literalinclude} code/ref-basics.saw
:lines: 13-26
:language: sawscript
:::

There are two interesting things worth calling out in this spec:

1. Instead of allocating the reference values with `mir_alloc`, we instead use
   `mir_alloc_mut`. This is a consequence of the fact that `&mut u32` is a
   different type from `&mut` in Rust (and in MIR), and and such, we need a
   separate `mir_alloc_mut` to get the types right.
2. This spec features calls to `mir_points_to` before _and_ after
   `mir_execute_func`. This is because the values that `a_ref` and `b_ref` point
   to before calling the function are different than the values that they point
   to after calling the function. The two uses to `mir_points_to` after the
   function has been called swap the order of `a_val` and `b_val`, reflecting
   the fact that the `swap` function itself swaps the values that the references
   point to.

### Convenience: `mir_ref_of` and `mir_ref_of_mut`

Because this pattern of allocating a reference and initializing it with
`mir_points_to` is so common, SAW provides helpers: `mir_ref_of` for immutable
references and `mir_ref_of_mut` for mutable references.

:::{code-block} console
sawscript> :type mir_ref_of
MIRValue -> MIRSetup MIRValue
:::

`mir_ref_of` combines `mir_alloc` and `mir_points_to` into a single operation,
returning a reference to the specified value. Likewise `mir_ref_of_mut`
combines `mir_alloc_mut` and `mir_points_to`. This portion of a spec:

:::{code-block} console
s <- mir_alloc (mir_adt s_adt);
s_val <- mir_fresh_expanded_value "s_val" (mir_adt s_adt);
mir_points_to s s_val;
:::

can be rewritten more concisely as:

:::{code-block} console
s_val <- mir_fresh_expanded_value "s_val" (mir_adt s_adt);
s <- mir_ref_of s_val;
:::

This version mirrors how one would write the function in Rust, where a `&T`
points to an already-initialized value. Using `mir_ref_of` encourages that 
style and avoids the risk of forgetting to initialize allocated memory.
