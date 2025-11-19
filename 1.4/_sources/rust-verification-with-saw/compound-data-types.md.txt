# Compound data types

Besides integer types and reference types, Rust also features a variety of other
interesting data types. This part of the tutorial will briefly go over some of
these data types and how to interface with them in SAW.

## Array types

Rust includes array types where the length of the array is known ahead of time.
For instance, this `index` function takes an `arr` argument that must contain
exactly three `u32` values:

:::{literalinclude} code/arrays.rs
:lines: 1-3
:language: rust
:::

While Rust is good at catching many classes of programmer errors at compile
time, one thing that it cannot catch in general is out-of-bounds array
accesses. In this `index` example, calling the function with a value of `idx`
ranging from `0` to `2` is fine, but any other choice of `idx` will cause the
program to crash, since the `idx` will be out of the bounds of `arr`.

SAW is suited to checking for these sorts of out-of-bound accesses. Let's write
an incorrect spec for `index` to illustrate this:

:::{literalinclude} code/arrays-fail.saw
:lines: 3-14
:language: sawscript
:::

Before we run this with SAW, let's highlight some of the new concepts that this
spec uses:

1. The type of the `arr` variable is specified using `mir_array 3 mir_u32`.
   Here, the `mir_array` function takes the length of the array and the element
   type as arguments, just as in Rust.
2. The spec declares the return value to be `{{ arr @ idx }}`, where `@` is
   Cryptol's indexing operator. Also note that it is completely valid to embed
   a MIR array type into a Cryptol expression, as Cryptol has a sequence type
   that acts much like arrays do in MIR.

As we hinted above, this spec is wrong, as it says that this should work for
_any_ possible values of `idx`. SAW will catch this mistake:

:::{code-block} console
$ saw arrays-fail.saw



[21:03:05.374] Loading file "arrays-fail.saw"
[21:03:05.411] Verifying arrays/47a26581::index[0] ...
[21:03:05.425] Simulating arrays/47a26581::index[0] ...
[21:03:05.426] Checking proof obligations arrays/47a26581::index[0] ...
[21:03:05.445] Subgoal failed: arrays/47a26581::index[0] index out of bounds: the length is move _4 but the index is _3
[21:03:05.445] SolverStats {solverStatsSolvers = fromList ["SBV->Z3"], solverStatsGoalSize = 53}
[21:03:05.445] ----------Counterexample----------
[21:03:05.445]   idx: 2147483648
[21:03:05.445] Stack trace:
"mir_verify" (arrays-fail.saw:14:1-14:11)
Proof failed.
:::

We can repair this spec by adding some preconditions:

:::{literalinclude} code/arrays.saw
:lines: 3-12
:language: sawscript
:::

An alternative way of writing this spec is by using SAW's `mir_array_value`
command:

:::{code-block} console
sawscript> :type mir_array_value
MIRType -> [MIRValue] -> MIRValue
:::

Here, the `MIRType` argument represents the element type, and the list of
`MIRValue` arguments are the element values of the array. We can rewrite
`index_spec` using `mir_array_value` like so:

:::{literalinclude} code/arrays.saw
:lines: 18-30
:language: sawscript
:::

Here, `[arr0, arr1, arr2]` is Cryptol notation for constructing a length-3
sequence consisting of `arr0`, `arr1`, and `arr2` as the elements.
`index_alt_spec` is equivalent to `index_spec`, albeit more verbose. For this
reason, it is usually preferable to use `mir_fresh_var` to create an entire
symbolic array rather than creating separate symbolic values for each element
and combining them with `mir_array_value`.

There are some situations where `mir_array_value` is the only viable choice,
however. Consider this variant of the `index` function:

:::{literalinclude} code/arrays.rs
:lines: 5-7
:language: rust
:::

When writing a SAW spec for `index_ref_arr`, we can't just create a symbolic
variable for `arr` using `mir_alloc (mir_array 3 ...)`, as the reference values
in the array wouldn't point to valid memory. Instead, we must individually
allocate the elements of `arr` using separate calls to `mir_alloc` and then
build up the array using `mir_array_value`. (As an exercise, try writing and
verifying a spec for `index_ref_arr`).

## Tuple types

Rust includes tuple types where the elements of the tuple can be of different
types. For example:

:::{literalinclude} code/tuples.rs
:lines: 1-3
:language: rust
:::

SAW includes a `mir_tuple` function for specifying the type of a tuple value.
In addition, one can embed MIR tuples into Cryptol, as Cryptol also includes
tuple types whose fields can be indexed with `.0`, `.1`, etc. Here is a spec
for `flip` that makes use of all these features:

:::{literalinclude} code/tuples.saw
:lines: 3-9
:language: sawscript
:::

SAW also includes a `mir_tuple_value` function for constructing a tuple value
from other `MIRValue`s:

:::{code-block} console
sawscript> :type mir_tuple_value
[MIRValue] -> MIRValue
:::

`mir_tuple_value` plays a similar role for tuples as `mir_array_value` does for
arrays.

## Struct types

Rust supports the ability for users to define custom struct types. Structs are
uniquely identified by their names, so if you have two structs like these:

:::{literalinclude} code/structs.rs
:lines: 1-2
:language: rust
:::

Then even though the fields of the `S` and `T` structs are the same, they are
_not_ the same struct. This is a type system feature that Cryptol does not
have, and for this reason, it is not possible to embed MIR struct values into
Cryptol. It is also not possible to use `mir_fresh_var` to create a symbolic
struct value. Instead, one can use the `mir_struct_value` command:

:::{code-block} console
sawscript> :type mir_struct_value
MIRAdt -> [MIRValue] -> MIRValue
:::

Like with `mir_array_value` and `mir_tuple_value`, the `mir_struct_value`
function takes a list of `MIRValue`s as arguments. What makes
`mir_struct_value` unique is its `MIRAdt` argument, which we have not seen up
to this point. In this context, "`Adt`" is shorthand for "[algebraic data
type](https://en.wikipedia.org/wiki/Algebraic_data_type)", and Rust's structs
are an example of ADTs. (Rust also supports enums, another type of ADT that we
will see later in this tutorial.)

ADTs in Rust are named entities, and as such, they have unique identifiers in
the MIR JSON file in which they are defined. Looking up these identifiers can
be somewhat error-prone, so SAW offers a `mir_find_adt` command that computes
an ADT's identifier and returns the `MIRAdt` associated with it:

:::{code-block} console
sawscript> :type mir_find_adt
MIRModule -> String -> [MIRType] -> MIRAdt
:::

Here, `MIRModule` correspond to the MIR JSON file containing the ADT
definition, and the `String` is the name of the ADT whose identifier we want to
look up. The list of `MIRType`s represent types to instantiate any type
parameters to the struct (more on this in a bit).

As an example, we can look up the `S` and `T` structs from above like so:

:::{literalinclude} code/structs.saw
:lines: 3-6
:language: sawscript
:::

We pass an empty list of `MIRType`s to each use of `mir_find_adt`, as neither
`S` nor `T` have any type parameters. An example of a struct that does include
type parameters can be seen here:

:::{literalinclude} code/structs.rs
:lines: 12
:language: rust
:::

As mentioned before, SAW doesn't support generic definitions out of the box, so
the only way that we can make use of the `Foo` struct is by looking up a
particular instantiation of `Foo`'s type parameters. If we define a function
like this, for example:

:::{literalinclude} code/structs.rs
:lines: 14-16
:language: rust
:::

Then this function instantiates `Foo`'s `A` type parameter with `u32` and the
`B` type parameter with `u64`. We can use `mir_find_adt` to look up this
particular instantiation of `Foo` like so:

:::{literalinclude} code/structs.saw
:lines: 7
:language: sawscript
:::

In general, a MIR JSON file can have many separate instantiations of a single
struct's type parameters, and each instantiation must be looked up separately
using `mir_find_adt`.

Having looked up `Foo<u32, u64>` using `mir_find_adt`, let's use the resulting
`MIRAdt` in a spec:

:::{literalinclude} code/structs.saw
:lines: 9-18
:language: sawscript
:::

Note that we are directly writing out the values `27` and `42` in Cryptol.
Cryptol's numeric literals can take on many different types, so in order to
disambiguate which type they should be, we give each numeric literal an
explicit type annotation. For instance, the expression `27 : [32]` means that
`27` should be a 32-bit integer.

### Symbolic structs

Let's now verify a function that takes a struct value as an argument:

:::{literalinclude} code/structs.rs
:lines: 18-22
:language: rust
:::

Moreover, let's verify this function for all possible `Bar` values. One way to
do this is to write a SAW spec that constructs a struct value whose fields are
themselves symbolic:

:::{literalinclude} code/structs.saw
:lines: 20-38
:language: sawscript
:::

This is a rather tedious process, however, as we had to repeatedly use
`mir_fresh_var` to create a fresh, symbolic value for each field. Moreover,
because `mir_fresh_var` does not work for structs, we had to recursively apply
this process in order to create a fresh `Foo` value. It works, but it takes a
lot of typing to accomplish.

To make this process less tedious, SAW offers a `mir_fresh_expanded_value`
command that allows one to create symbolic values of many more types. While
`mir_fresh_var` is limited to those MIR types that can be directly converted to
Cryptol, `mir_fresh_expanded_value` can create symbolic structs by automating
the process of creating fresh values for each field. This process also applies
recursively for struct fields, such as the `Foo` field in `Bar`.

As an example, a much shorter way to write the spec above using
`mir_fresh_expanded_value` is:

:::{literalinclude} code/structs.saw
:lines: 42-48
:language: sawscript
:::

That's it! Note that the string `"b"` is used as a prefix for all fresh names
that `mir_fresh_expanded_value` generates, so if SAW produces a counterexample
involving this symbolic struct value, one can expect to see names such as
`b_0`, `b_1`, etc. for the fields of the struct.

`mir_fresh_expanded_value` makes it easier to construct large, compound values
that consist of many smaller, inner values. The drawback is that you can't
refer to these inner values in the postconditions of a spec. As a result, there
are some functions for which `mir_fresh_expanded_value` isn't suitable, so keep
this in mind before reaching for it.

## Enum types

Besides structs, another form of ADT that Rust supports are enums. Each enum
has a number of different _variants_ that describe the different ways that an
enum value can look like. A famous example of a Rust enum is the `Option` type,
which is defined by the standard library like so:

:::{code-block} rust
enum Option<T> {
    None,
    Some(T),
}
:::

`Option` is commonly used in Rust code to represent a value that may be present
(`Some`) or absent (`None`). For this reason, we will use `Option` as our
motivating example of an enum in this section.

First, let's start by defining some functions that make use of `Option`'s
variants:

:::{literalinclude} code/enums.rs
:lines: 1-7
:language: rust
:::

Both functions return an `Option<u32>` value, but each function returns a
different variant. In order to tell these variants apart, we need a SAW
function which can construct an enum value that allows the user to pick which
variant they want to construct. The `mir_enum_value function does exactly that:

:::{code-block} console
sawscript> :type mir_enum_value
MIRAdt -> String -> [MIRValue] -> MIRValue
:::

Like `mir_struct_value`, `mir_enum_value` also requires a `MIRAdt` argument in
order to discern which particular enum you want. Unlike `mir_struct_value`,
however, it also requires a `String` which variant of the enum you want. In the
case of `Option`, this `String` will either be `"None"` or `"Some"`. Finally,
the `[MIRValue]` arguments represent the fields of the enum variant.

Let's now verify some enum-related code with SAW. First, we must look up the
`Option<u32>` ADT, which works just as if you had a struct type:

:::{literalinclude} code/enums.saw
:lines: 5
:language: sawscript
:::

Next, we can use this ADT to construct enum values. We shall use
`mir_enum_value` to create a `Some` value in the spec for `i_found_something`:

:::{literalinclude} code/enums.saw
:lines: 7-16
:language: sawscript
:::

Note that while we used the full identifier `core::option::Option` to look up
the `Option` ADT, we do not need to use the `core::option` prefix when
specifying the `"Some"` variant. This is because SAW already knows what the
prefix should be from the `option_u32` ADT, so the `"Some"` shorthand suffices.

Similarly, we can also write a spec for `i_got_nothing`, which uses the `None`
variant:

:::{literalinclude} code/enums.saw
:lines: 18-25
:language: sawscript
:::

### Symbolic enums

In order to create a symbolic struct, one could create symbolic fields and pack
them into a larger struct value using `mir_struct_value`. The same process is
not possible with `mir_enum_value`, however, as a symbolic enum value would
need to range over _all_ possible variants in an enum.

Just as `mir_fresh_expanded_value` supports creating symbolic structs,
`mir_fresh_expanded_value` also supports creating symbolic enum values. For
example, given this function that accepts an `Option<u32>` value as an
argument:

:::{literalinclude} code/enums.rs
:lines: 9-11
:language: rust
:::

We can write a spec for this function that considers all possible `Option<u32>`
values like so:

:::{literalinclude} code/enums.saw
:lines: 27-33
:language: sawscript
:::

Here, `o` can be a `None` value, or it can be a `Some` value with a symbolic
field.

## Slices

Slices are a particular type of reference that allow referencing contiguous
sequences of elements in a collection, such as an array. Unlike ordinary
references (e.g., `&u32`), SAW does not permit allocating a slice directly.
Instead, one must take a slice of an existing reference. To better illustrate
this distinction, consider this function:

:::{literalinclude} code/slices.rs
:lines: 1-3
:language: rust
:::

`sum_of_prefix` takes a slice to a sequence of `u32`s as an argument, indexes
into the first two elements in the sequence, and adds them together. There are
many possible ways we can write a spec for this function, as the slice argument
may be backed by many different sequences. For example, the slice might be
backed by an array whose length is exactly two:

:::{literalinclude} code/slices.rs
:lines: 6-8
:language: rust
:::

We could also make a slice whose length is longer than two:

:::{literalinclude} code/slices.rs
:lines: 10-12
:language: rust
:::

Alternatively, the slice might be a subset of an array whose length is longer
than two:

:::{literalinclude} code/slices.rs
:lines: 14-16
:language: rust
:::

All of these are valid ways of building the slice argument to `sum_of_prefix`.
Let's try to write SAW specifications that construct these different forms of
slices. To do so, we will need SAW functions that take a reference to a
collection (e.g., an array) and converts them into a slice reference. The
`mir_slice_value` function is one such function:

:::{code-block} console
sawscript> :type mir_slice_value
MIRValue -> MIRValue
:::

`mir_slice_value arr_ref` is the SAW equivalent of writing `arr_ref[..]`. That
is, if `arr_ref` is of type `&[T; N]`, then `mir_slice_value arr_ref` is of
type `&[T]`. Note that `arr_ref` must be a _reference_ to an array, not an
array itself.

Let's use `mir_slice_value` to write a spec for `sum_of_prefix` when the slice
argument is backed by an array of length two:

:::{literalinclude} code/slices.saw
:lines: 5-15
:language: sawscript
:::

The first part of this spec allocates an array reference `a_ref` and declares
that it points to a fresh array value `a_val`. The next part declares a slice
`s` that is backed by the entirety of `a_ref`, which is then passed as an
argument to the function itself. Finally, the return value is declared to be
the sum of the first and second elements of `a_val`, which are the same values
that back the slice `s` itself.

As noted above, the `sum_of_prefix` function can work with slices of many
different lengths. Here is a slight modification to this spec that declares it
to take a slice of length 5 rather than a slice of length 2:

:::{literalinclude} code/slices.saw
:lines: 19-29
:language: sawscript
:::

Both of these examples declare a slice whose length matches the length of the
underlying array. In general, there is no reason that these have to be the
same, and it is perfectly fine for a slice's length to be less than the the
length of the underlying array. In Rust, for example, we can write a slice of a
subset of an array by writing `&arr_ref[0..2]`. The SAW equivalent of this can
be achieved with the `mir_slice_range_value` function:

:::{code-block} console
sawscript> :type mir_slice_range_value
MIRValue -> Int -> Int -> MIRValue
:::

`mir_slice_range_value` takes takes two additional `Int` arguments that
represent (1) the index to start the slice from, and (2) the index at which the
slice ends. For example, `mir_slice_range_value arr_ref 0 2` creates a slice
that is backed by the first element (index `0`) and the second element (index
`1`) of `arr_ref`. Note that the range `[0..2]` is half-open, so this range
does _not_ include the third element (index `2`).

For example, here is how to write a spec for `sum_of_prefix` where the slice is
a length-2 subset of the original array:

:::{literalinclude} code/slices.saw
:lines: 33-43
:language: sawscript
:::

Note that both `Int` arguments to `mir_slice_range_value` must be concrete
(i.e., not symbolic). (See the section below if you want an explanation for why
they are not allowed to be symbolic.)

### Aside: slices of arbitrary length

After reading the section about slices above, one might reasonably wonder: is
there a way to write a more general spec for `sum_of_prefix`: that covers all
possible slice lengths `n`, where `n` is greater than or equal to 2? In this
case, the answer is "no".

This is a fundamental limitation of the way SAW's symbolic execution works. The
full reason for why this is the case is somewhat technical (keep reading if you
want to learn more), but the short answer is that if SAW attempts to
simulate code whose length is bounded by a symbolic integer, then SAW will go
into an infinite loop. To avoid this pitfall, the `mir_slice_range_value`
function very deliberately requires the start and end values to be concrete
integers, as allowing these values to be symbolic would allow users to
inadvertently introduce infinite loops in their specifications.

A longer answer as to why SAW loops forever on computations that are bounded by
symbolic lengths: due to the way SAW's symblolic execution works, it creates a
complete model of the behavior of a function for all possible inputs. The way
that SAW achieves this is by exploring all possible execution paths through a
program. If a program involves a loop, for example, then SAW will unroll all
iterations of the loop to construct a model of the loop's behavior. Similarly,
if a sequence (e.g., a slice or array) has an unspecified length, then SAW must
consider all possible lengths of the array.

SAW's ability to completely characterize the behavior of all paths through a
function is one of its strengths, as this allows it to prove theorems that
other program verification techniques would not. This strength is also a
weakness, however. If a loop has a symbolic number of iterations, for example,
then SAW will spin forever trying to unroll the loop. Similarly, if a slice
were to have a symbolic length, then SAW would spin forever trying to simulate
the program for all possible slice lengths.

In general, SAW cannot prevent users from writing programs whose length is
bounded by a symbolic value. For now, however, SAW removes one potential
footgun by requiring that slice values always have a concrete length.
