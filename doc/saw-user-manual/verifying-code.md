(verifying-code)=
# Verifying Code Using Symbolic Execution

Proving things about Cryptol models can be quite useful; however, as
discussed before, the most common use case for SAW is probably
verifying code against a Cryptol model.
There are three parts to this: writing the specification to verify
against, loading the code to verify, and then running the
verification.
The specification is the most complicated part of this, so we'll
take it up first.

There are three symbolic execution backends in SAW; they all wrap
different languages around the Crucible symbolic execution engine.
They handle LLVM bitcode, Java byte code, and Rust's MIR
intermediate representation.
(There is also a fourth experimental backend, interconnected with the
LLVM backend, that handles raw x86_64 binaries.)

Each of these has its own collection of SAWScript builtins; the three
sets of builtins are very similar but not quite identical.
Similarly, when using the Python bindings each has its own interface,
and the three are very similar but not quite identical.

## Simple Example for Getting Started

:::{warning}
This section is under construction!
:::


<!-- ------------------------------------------------------------ -->


## Languages for Specifications

Each backend also has its own specification language.
This is necessary because all three backends execute code in a
wider world than Cryptol and SAWCore.
SAWCore is a pure lambda calculus; Cryptol is largely restricted to
finite objects.
LLVM, Java, and Rust all operate in a world that has pointers, memory
allocation, mutable state, global variables, partial functions where
some combinations of inputs may be invalid, and other real-world
phenomena.
All three of them also (and not uncoincidentally) have a broader set
of types than either Cryptol or SAWCore, such as pointers.

Consequently, each backend has its own language that includes these
types and their values.
This is the language that specifications for code in that backend must
be written in, and those specifications must typecheck in that
language.
In each case it is, like the specification languages for other
production language verification frameworks, akin to but not quite the
same as a pure subset of the original source language.

Unfortunately, at least for the time being, the backend specification
languages are entirely implicit.
The types and values of these languages appear as SAWScript program
objects, but they have no concrete syntax.

Instead, types and values are assembled programmatically, and then
assertions and specifications are assembled programmatically out of
those.
Values can be lifted out of Cryptol (and/or SAWCore) as needed.
In the typical case of verifying code against a Cryptol model, the
specification works by lifting the results of Cryptol-level
computations into the specification language and relating them to the
results produced by the target code.

There is thus an implicit correspondence between Cryptol types and
certain types in each backend, and SAWScript operations that lift
Cryptol values to specification-language values according to this
correspondence.

The SAWScript type of LLVM type objects in the LLVM backend is
`LLVMType`; the SAWScript type of LLVM value objects is `LLVMValue`.
The function `llvm_term` lifts a Cryptol-level value of SAWScript type
`Term` to an LLVM value object of type `LLVMValue`.

Similarly, in the JVM backend, types appear as `JavaType`, values as
`JVMValue`, and the value-lifting function is `jvm_term`.
In the MIR backend, types are `MIRType`, values are `MIRValue`, and
the lifting function is `mir_term`.

<!--
   There are no type-lifting functions (there's an `llvm_type` but it
   does something different), presumably because types are typically
   too static for it to be very useful.

   I wonder, though, if it would reduce confusion to add type-lifting
   functions (e.g `mir_type : Type -> MIRType`); it would make the
   embedding more explicit and thus perhaps easier to follow ...
-->

Users frequently find this embedding, these functions, and the
sometimes apparently arbitrary need for their use confusing.
It is important to build a robust mental model of the multiple
layers involved and how the mapping between them works.
Cryptol values can be lifted to LLVM, JVM, or MIR values, and
SAWScript is its own layer above both.

Rather than diving directly into the implicit backend languages
(including the details of those mappings) without context, we'll first
look in a general way at how specifications for code work.

## Specifications

Given the above, it should be clear that in general the specification
for an LLVM, JVM, or MIR function is more involved than just naming a
corresponding Cryptol function, even if that Cryptol function is a
complete behavioral specification.

SAW specifications for these backends (sometimes, somewhat
inaccurately, also called "Crucible specifications") each set up a
call to the target function.
This involves creating symbolic variables, defining the setup needed
to make a call (called the _prestate_), providing (generally symbolic)
arguments to the function, and then defining the expected results
(called the _poststate_).

Defining the prestate and poststate can each be subdivided into two
parts: first, allocating memory, and second, making assertions about
symbolic variables and the contents of memory (called _preconditions_
and _postconditions_ respectively).
The prestate and poststate logic are divided by the argument
specification.
This can be thought of as the declaration of the function arguments;
it can also be thought of as the point in the specification where the
target function gets invoked.
There is a specific builtin for this in each back end; for example,
in the LLVM backend it is `llvm_execute_func`.
There must be exactly one call to this builtin in each specification.

Each backend provides a set of operations for creating symbolic (also
called _fresh_) variables of various types.
In general you want to prove that your function behaves a certain
way for all valid inputs; the premise of verification via symbolic
execution is that we can execute on inputs that range over many
possible values.

Generally, for base types symbolic values can be generated at the
Cryptol level and then lifted into the code specification layer.
For complex types that have no Cryptol analogues, symbolic values can
be created either by constructing specification-level values from
symbolic base values (so for example, one might create a struct with
two integer fields from two symbolic integer values lifted into the
specification layer) or with convenience functions that create complex
values and fill them with fresh values.

While in general fresh variables are created at the beginning of a
specification (because these would be the quantifier-bound variables
if the specification were written declaratively as a theorem) it is
also possible to create new ones in the poststate logic.
These are treated as outputs; essentially they're existentially
bound in the output part of the specification.

Pointers and references (other than null or uninitialized pointers, in
backends where they exist) must be created by explicitly allocating
memory.
Allocations done in the prestate logic are presumed to have been done
before the function call, and the existence of those allocations is
part of the overall precondition.
Allocations done in the poststate logic are presumed to be done _by_
the function call, and the resulting pointers are treated as outputs.

Each distinct memory region must be allocated separately, and
separately allocated memory regions are (by default, with some
exceptions) presumed to be distinct.

In situations where a function takes multiple pointer arguments that
might or might not alias, it is usually necessary to write multiple
specifications to cover the different cases.

Assertions relate symbolic variables to other symbolic variables, or
to constants, or to computations from a Cryptol model.
Assertions in the prestate logic create obligations that must be
satisfied to make the call to the function; the function's code is
thus entitled to assume they hold.
Assertions in the poststate logic create obligations that the function
must satisfy.

The return value of the function (if any) is specified in the
poststate as a special kind of assertion.

<!-- XXX this should talk about freeing memory -->

This is all very abstract, so as an example, consider the following
somewhat silly C code:

```c
#include <stdlib.h>

unsigned *add(unsigned *x, unsigned *y) {
   unsigned *ret;

   ret = malloc(sizeof(*ret));
   *ret = *x + *y;
   return ret;
}
```

The function `add` takes two pointers to integers, and returns a
pointer to a newly allocated integer that holds the sum.
We use unsigned integers to avoid having to worry about whether
the addition overflows, which would be undefined for signed
integers.

We can write the following LLVM specification for it, which has
all of the elements discussed above:

```sawscript
let add_spec = do {
   xval <- llvm_fresh_var "xval" (llvm_int 32);
   yval <- llvm_fresh_var "yval" (llvm_int 32);

   x <- llvm_alloc (llvm_int 32);
   y <- llvm_alloc (llvm_int 32);

   llvm_points_to x (llvm_term xval);
   llvm_points_to y (llvm_term yval);

   llvm_execute_func [x, y];

   ret <- llvm_alloc (llvm_int 32);

   llvm_points_to ret (llvm_term {{ xval + yval }});
   llvm_return ret;
};
```

The specification is always a SAWScript do-block, which will be
executed top-to-bottom when we run the verification.

First we create two symbolic variables `xval` and `yval` to hold
the values pointed to by the pointers `x` and `y`.
These are 32-bit LLVM integers; however, `llvm_fresh_var` creates
them at the Cryptol level and the SAWScript `xval` and `yval`
variables have type `Term`.

Then we allocate memory for the prestate.
On entry, we want both pointers to be valid.
In this specification we presume they should be disjoint, so we do two
separate allocations, one for `x` and one for `y`.
This gives us two pointer values.

(This will not match later calls to `add` that pass the same pointer
as both arguments.
If we want to allow that, we need a second spec that allocates
only one pointer and therefore also has only one fresh value.
Writing this spec by cutting down the one above should be a
fairly straightforward exercise.)

Then we assert the prestate conditions: `x` points to `xval` and
`y` points to `yval`.
We need to lift `xval` and `yval` to the LLVM level with `llvm_term`
because, as noted above, `llvm_fresh_var` created them at the Cryptol
level.

Then we call the function and pass `x` and `y` as the arguments.
We do not need `llvm_term` here because `x` and `y`, being pointers,
are already LLVM-level values.

The rest of the spec is poststate logic: first we allocate another
pointer for the return value (matching the allocation within the
function).
Then we assert that it points to, not another fresh variable but
the sum of the existing ones, whatever that is.
We can write that sum in a Cryptol block that refers to `xval` and
`yval` precisely because those are Cryptol-level variables with
Cryptol types.
We wrap the Cryptol block in `llvm_term` because the Cryptol block is,
unsurprisingly, a Cryptol-level value and needs to be lifted into the
LLVM world.

The final line specifies that the return value of the function is
the pointer `ret`.
This is a special kind of poststate assertion.
(You must provide a return value if the function returns a value.
You must not if it doesn't.
C and Java functions of return type `void` do not.
Rust functions of return type `()` can be construed either way:
you can specify that the return value is `()`, but you need not.)
If you don't want to specify the return value exactly, you can create
a fresh value for it in the poststate logic and return that, optionally
restricting its value to a subset of possible values if desired.

<!--
:::{code-block} sawscript
do {
  ...
  {llvm,jvm,mir}_execute_func <args>;
  ...
  ret <- {llvm,jvm,mir}_fresh_var "ret" <type>;
  {llvm,jvm,mir}_return ({llvm,jvm,mir}_term ret);
}
:::
-->

We again don't need `llvm_term` with `ret` because it's an LLVM-level
value.

In order to actually verify this function we also need to compile
the C code:

```shell
clang -g -c -emit-llvm example.c -o example.bc
```

and we need two additional lines along with the specification itself
in a SAWScript file:

```sawscript
bc <- llvm_load_module "example.bc";
llvm_verify bc "add" [] true add_spec z3;
```

This loads the compiler output, giving us an LLVM module handle `bc`,
and them runs the verification by calling `llvm_verify`.

(Note that `jvm_verify` and `mir_verify` are essentially the same,
except that they work with JVM and MIR code modules and specs.)

Running SAW on the resulting file gives the following output:
```console
Loading file "example.saw"
Verifying add...
Simulating add...
Checking proof obligations add...
Proof succeeded! add
```

The arguments to `llvm_verify` are, first, the LLVM module handle; the
name of the function; a list of what we call _override_ specifications
(more on that in a moment), a flag that says whether to enable path
satisfiability checking (leave this set to true for now), the
specification, and a proof script.

### Overrides and Compositional Verification

`llvm_verify` returns a SAWScript value of type `LLVMSpec`.
This represents a proved/verified specification.
Here we ignore it; in a larger development you would likely capture
it for later use.

This function does not call any other functions.
However, imagine a function that calls `add`.
When verifying _that_ function, we could let the symbolic execution
engine execute directly into `add`, or we could provide the
specification for `add` that we just proved and have it apply that
instead.
Such specifications are called _override_ specifications, because
they override the direct execution of the function specified.

In the case of `add`, using the proved specification to override later
executions probably is no faster than just executing the function
directly, and might even be slower.
However, for functions that do a lot of work, applying the proved
specification will require a lot less computation than, essentially,
redoing it every time.
The use of override specifications is critical for verifying
nontrivial code.
This is called _compositional verification_ because it allows
composing specifications for different chunks of code.

If you want to use a proved specification as an override when calling
`llvm_verify` (or `jvm_verify` or `mir_verify`), you can put it in the
list that's empty in the example above.

It is also possible to write specifications and assume that they're
valid instead of prove them, and then use them as overrides.
This is useful for library code, where you might not have the source
or where verifying the library is a whole additional project.
The LLVM function for this is `llvm_unsafe_assume_spec`; it is akin
to `llvm_verify` but takes only the LLVM module handle, function name,
and spec.
(There are corresponding `jvm_unsafe_assume_spec` and
`mir_unsafe_assume_spec` functions as well.)

(One might instead think to provide a proof script that just admits
all goals given to it.
However, that will still run the symbolic execution, which still
requires most of the specification setup and can still fail, so in
practice it isn't useful.)

### Additional Restrictions on Arrays

<!--
   This is not a great place to put this but there's not much choice
   in the current layout.
--> 

In all three backends the type construction for arrays requires a
concrete SAWScript integer.
Proof results are thus dependent on the array size being as indicated,
and may not hold for other sizes.

Note however that it is intended to be possible to pass an array of
length _M_ to a function that expects a length _N_, where _M_ > _N_,
such that the function will just ignore the extra space.

In cases where this is not sufficient, it is also possible to make
the specification a function parameterized by the length _N_ and then
prove it repeatedly for different sizes.
See [the SAWScript programming chapter](#sawscript).

### Summary

A specification is a SAWScript do-block divided into two parts by the
call to `llvm_execute_func`, `jvm_execute_func`, or
`mir_execute_func`, which provides the arguments to the function being
verified.
The first half of the block contains prestate logic for creating fresh
variables, allocating memory, and setting up the allowable start states.
The second half of the block contains poststate logic for
(potentially) creating more fresh variables, allocating more memory,
and specifying the allowable output states.

We can now go into each backend's implicit specification language
and its driving SAWScript builtins in more detail.
Each backend has its own types and values, and its own SAWScript
functions.
However, there is a good deal of commonality across the backends.


<!-- ------------------------------------------------------------ -->


## The LLVM Backend and LLVM Specifications

<!--
   XXX we don't need to introduce e.g. all the llvm_points_to variants.
   Many of them, and some of the other stuff in here, should get moved
   to an LLVM Backend Reference section.
-->

In the LLVM backend, types appear in SAWScript as values of SAWScript
type `LLVMType`, and values have the SAWScript type `LLVMValue`.
LLVM code modules have the type `LLVMModule`, and the specification
do-blocks have the type `LLVMSetup ()`.

The function argument declaration that divides the pre- and post-
portions of a specification is done with `llvm_execute_func`.

(llvm-types)=
### LLVM Types

The following SAWScript functions construct LLVM types:

- `llvm_int` _`n`_ produces an _`n`_-bit-wide machine integer/bitvector.
  Like Cryptol, SAW doesn't have separate signed and unsigned
  bitvector types.
  The `llvm_int` types correspond to the Cryptol bitvector types `[`_`n`_`]`.
  Lifting a Cryptol bitvector value to an LLVM value produces a value
  of this type.

- `llvm_float` is the type of (32-bit) single-precision floating point
  numbers, and `llvm_double` is the type of (64-bit) double-precision
  floating point numbers.
  These correspond to the Cryptol floating point types of the proper
  sizes.
  However, SAW's support for floating point is rudimentary so these
  types are currently of little use.

  <!--
      XXX: there's no `llvm_quad` yet I guess...?
      IIRC LLVM also supports x86 80-bit floats.
  -->

- `llvm_array` _`n`_ _`ty`_ produces an array type of element type _`ty`_
  that is _`n`_ entries long.
  This type corresponds to the Cryptol sequence type `[`_`n`_`][`_`cty`_`]`
  where _`cty`_ is the Cryptol type corresponding to _`ty`_, if it exists.
  Lifting a Cryptol sequence value to an LLVM value produces a value
  of this type.
  (Note that Cryptol bitvectors are also sequences.
  A Cryptol sequence of `Bit` / `Bool` is a bitvector and lifts to
  `llvm_int` of some size.
  A Cryptol sequence of some other type lifts to an `llvm_array`.)

- `llvm_struct_type` _`tys`_ produces a struct type whose elements
  have types _`tys`_.
  _`tys`_ is a list of `LLVMType`.
  This corresponds to a Cryptol tuple type containing the Cryptol
  types corresponding to _`tys`_, if they exist.
  <!--
     XXX: what does `llvm_term` on a tuple produce? Is it packed,
     unpacked, or have we jacked the typechecking so it can be
     either?
  -->

- `llvm_packed_struct_type` _`tys`_ is like `llvm_struct_type` but
  produces a packed struct type.
  (That is, one that has no alignment padding between members.)
  This also corresponds to a Cryptol tuple type containing the
  Cryptol types corresponding to _`tys`_, if they exist.

- `llvm_pointer` _`ty`_ is the type of a pointer to _`ty`_.
  This has no Cryptol equivalent.

Furthermore,

- `llvm_type` takes a string in LLVM's type syntax and produces the
  corresponding `LLVMType`.
  For example, `llvm_type` `"i32"` produces the same type as
  `llvm_int` `32`.

- `llvm_alias` takes a string that's the name of a type alias and
  looks up the `LLVMType` for it.
  <!--
     XXX it doesn't take an LLVM module; where does it look for it?
     Inside a spec there's implicitly an LLVMModule in context, but
     this function is pure and isn't tied to LLVMSetup.
  -->

When your LLVM module is the result of compiling C code, all ordinary
C integer types map to the `llvm_int` type of the proper size.

The C `bool` type may appear as either `llvm_int` `1` or `llvm_int` `8`,
depending on context: loose `bool`s are generally `llvm_int` `1`, but
members of structs and arrays will usually be `llvm_int` `8`.
This is due to a peculiarity in the way Clang compiles `bool` down to
LLVM.
When in doubt about how a `bool` is represented, check the LLVM
bitcode by compiling your code with `clang -S -emit-llvm`.

### LLVM Values

The primary way to produce LLVM values of base type is to lift
Cryptol values with `llvm_term`.
For example, `llvm_term {{ 123 : [32] }}` produces an LLVM value
whose type is `llvm_int` `32`.

LLVM values of compound type can be constructed with these functions:

- `llvm_array_value` _`vals`_ constructs an LLVM array value; _`vals`_ is
  a list of values to put in the array.

- `llvm_struct_value` _`vals`_ constructs an LLVM struct value; _`vals`_ is
  a list of values to put in the struct, in order.

- `llvm_packed_struct_value` _`vals`_ is like `llvm_struct_value` but
  produces a packed struct.

The elements of LLVM values of compound type can be extracted with these
functions:

- `llvm_elem` _`val`_ _`n`_ extracts element _`n`_ of the LLVM array
  or struct (or packed struct) _`val`_.
  However, it only works on pointers: _`val`_ should be a pointer that
  points at an array or struct, and the returned value is a pointer to
  the element.
  There is no way <!-- AFAIK --> to extract elements from an array or
  struct value directly.

- `llvm_field` _`val`_ _`f`_ extracts the named field _`f`_ of a struct or
  packed struct _`val`_.
  Like `llvm_elem`, it only works on pointers.
  The LLVM module that defines the type must have been compiled with
  debugging information.
  Sometimes also the debugging information is insufficient to identify the
  correct type, in which case one should fall back to `llvm_elem`.

- `llvm_union` _`val`_ _`f`_ is like `llvm_field` except that it operates on
  a union.
  It too only works on pointers, and the LLVM module that defines the
  type must likewise have been compiled with debugging information.
  Note that because the address of a union is the same as the address of all
  its members, this function only changes the type of the pointer.
  One can use `llvm_cast_pointer` instead.
  However, `llvm_union` avoids baking in the identity of the type of
  the union field, which is both convenient and improves robustness.

### Binding Quantified Variables in LLVM

The basic function for this in the LLVM backend is
`llvm_fresh_var` _`x_` _`ty`_.
_`x`_ provides an internal name for the variable; _`ty`_ names its
type.
This type is an LLVM type (a value of type `LLVMType`) rather than
a Cryptol type.
However, it must be an LLVM type that has a corresponding Cryptol
type, because the result is a Cryptol-level SAWScript value.
(Thus, it has type `Term` and not type `LLVMValue`.)

For example:

```sawscript
x <- llvm_fresh_var "x" (llvm_int 32);
```

This produces a fresh 32-bit machine integer.

There is also an experimental function `llvm_fresh_cryptol_var` that
takes a Cryptol type instead.

It is reasonable to use the same identifier for the internal name and
for the SAWScript variable, and, where applicable, to make it the same
name as used for the same thing in the code under verification.

<!--
   XXX: currently it's possible to use the same internal name for
   multiple variables. This is a consequence of #3060 and not
   something we want to advertise.
-->

The function `llvm_fresh_expanded_val` _`ty`_ creates a fresh value of
LLVM-level type (thus, the type argument is an `LLVMType`) and populates
it recursively with fresh variables.
This can be used for struct and array types.

In general for values of compound type it is possible to create fresh
primitive values for the elements and create compound values with
functions like `llvm_array_value`; it is also possible to use
`llvm_fresh_expanded_val` and reason about the contents by using
functions like `llvm_elem`.
Which is preferable is in most cases purely a matter of convenience.

### Allocation and Pointers in the LLVM Backend

LLVM pointer values, other than null and uninitialized ones, cannot be
arbitrarily created; one must in general explicitly allocate memory to
create a pointer.
The pointer can then be passed as an argument to the function under
verification, or used to initialize other values.
Pointers allocated in the prestate logic are presumed to exist before
the function is called; pointers allocated (in the `llvm_alloc` sense)
in the poststate logic are expected to be allocated (in the `malloc`
runtime sense) by the function.

There are two chief exceptions to pointers needing to be allocated:

- `llvm_null` is a null pointer.

- `llvm_fresh_pointer` creates a pointer that does not point to anything.
  Accessing it is an error.
  This provides a useful simplification for functions that handle, but
  do not dereference, pointers.

<!--
   We don't have any particular story for places in systems code where
   you need to just write down pointers. However, this isn't the place
   to take that up.
-->

In the LLVM backend the primary allocation function is `llvm_alloc`.
It takes an LLVM-level type (a value of type `LLVMType`), allocates
memory to hold a value of that type, and produces an `LLVMValue`
representing the pointer.

Note that allocating memory and reasoning about its contents are
separate steps.
In most cases each `llvm_alloc` should be paired with an `llvm_points_to`
assertion (see below) that says something about the value found in the
allocated memory.
(Otherwise the memory is treated as uninitialized, and attempts to read
from it will be treated as an error.
Sometimes this is what you want; for example, a pointer argument whose
purpose is to return a complex value should not be read from before it's
written to, and thus leaving its contents uninitialized allows detecting
such mistakes.)

There are multiple variants of `llvm_alloc`:

- `llvm_alloc_aligned` takes an extra integer argument _`n`_ that's a
  power of 2, and allocates memory that's guaranteed to be aligned
  to an _`n`_-byte boundary.

- `llvm_alloc_readonly` creates a pointer that cannot be used for
  writing, like `const` pointers in C.
  The aliasing restrictions for allocations are relaxed for regions
  allocated with this function: read-only regions are allowed to
  alias one another.
  <!-- XXX: that needs more explanation. What does it mean in practice? -->

- `llvm_alloc_readonly_aligned` is like both `llvm_alloc_aligned` and
  `llvm_alloc_readonly` at once.

- `llvm_alloc_with_size` takes an extra integer argument, which must
  be greater than the size of the type, and allocates that much
  memory.
  This is useful for dealing with types that are headers for memory
  blocks.

- `llvm_alloc_sym_init` is like `llvm_alloc` but also implicitly
  fills the allocated memory with fresh byte values.

- `llvm_symbolic_alloc` takes three arguments: a boolean, which
  if true makes the allocation read-only like `llvm_alloc_readonly`,
  a power-of-two integer, which specifies the alignment like in
  `llvm_alloc_aligned`, and instead of a type the third argument
  is a size in bytes.

There is also a function `llvm_cast_pointer` that takes a pointer
value and an LLVM type, and yields a new pointer value with an updated
pointed-to type.
This is mostly useful for accessing pointers to unions in cases where
`llvm_union` isn't available.
Unsafe or undefined accesses constructed via pointer casts will fail.

### LLVM Global Variables

The LLVM world includes global (including file-static) variables.
Some of these get put in the data segment are mutable, and others
get put in read-only data and cannot be changed at runtime.
(Typically, globals declared in C with `const` end up in read-only
data, but there are some corner cases where that isn't true.
If in doubt, check in the LLVM bitcode whether the variable is
marked `constant`, or check the section in the output object file.)

By default, immutable global variables are always available for use,
and mutable globals that a function doesn't touch can be ignored.
However, each mutable global variable used by a function under
verification must be explicitly enabled in its specification.

This requirement arises because using a mutable global variable
creates an obligation to reason about its state.
Explicitly enabling mutable globals allows SAW to easily check that
all variables used are enabled, and all variables enabled have been
covered in both the pre-state and post-state assertions.

The function `llvm_alloc_global` _`name`_ enables the mutable global
_`name`_.
It returns nothing (not a pointer).
(The name arises because under the covers it does actually allocate: it
sets up the data-segment memory for the variable.)

To refer to the global, use the function `llvm_global` _`name`_; this
returns a pointer to it.

If you want the initializer value for a global, you can get it with
`llvm_global_initializer` _`name`_.
Sometimes this will be the prestate value you want, more often not.

For example, consider this code:

<!-- This matches intTests/test0036_globals/test-signed.c -->
:::{code-block} c
int x = 0;

int f(int y) {
  x = x + 1;
  return x + y;
}

int g(int z) {
  x = x + 2;
  return x + z;
}
:::

The following specifications are rejected because they do not allocate
the global `x`.
(And, even if they did, they provide neither a prestate value nor a
poststate value for it.)

<!-- This matches intTests/test0036_global/test-signed-fail.saw -->
:::{code-block} sawscript
m <- llvm_load_module "./test.bc";

f_spec <- llvm_verify m "f" [] true (do {
    y <- llvm_fresh_var "y" (llvm_int 32);
    llvm_execute_func [llvm_term y];
    llvm_return (llvm_term {{ 1 + y : [32] }});
}) abc;

g_spec <- llvm_verify m "g" [] true (do {
    z <- llvm_fresh_var "z" (llvm_int 32);
    llvm_execute_func [llvm_term z];
    llvm_return (llvm_term {{ 2 + z : [32] }});
}) abc;
:::

If we want to assume that `f` will only be called once and never have
`g` written before it, we could write this spec:

<!-- This matches intTests/test0036_global/test-signed.saw -->
:::{code-block} sawscript
m <- llvm_load_module "./test.bc";


let init_global name = do {
  llvm_alloc_global name;
  llvm_points_to (llvm_global name)
                 (llvm_global_initializer name);
};

f_spec <- llvm_verify m "f" [] true (do {
    y <- llvm_fresh_var "y" (llvm_int 32);
    init_global "x";
    llvm_precond {{ y < 2^^31 - 1 }};
    llvm_execute_func [llvm_term y];
    llvm_return (llvm_term {{ 1 + y : [32] }});
}) abc;
:::

which initializes `x` to whatever it is initialized to in the C code at
the beginning of verification.
(It also includes a constraint on the argument `y` to avoid undefined
behavior arising from signed integer overflow.)
However, it does not specify an output value for `x` so it cannot be
used compositionally.

We could also write this more complete spec:

<!-- This does not match anything committed in test0036_global (yet) -->
:::{code-block} sawscript
m <- llvm_load_module "test-signed.bc";

f_spec <- llvm_verify m "f" [] true (do {
    x <- llvm_fresh_var "x" (llvm_int 32);
    y <- llvm_fresh_var "y" (llvm_int 32);
    llvm_alloc_global "x";
    llvm_points_to (llvm_global "x") (llvm_term x);
    llvm_precond {{ x + y < 2^^31 - 1 }};
    llvm_execute_func [llvm_term y];
    llvm_points_to (llvm_global "x") (llvm_term {{ 1 + x : [32] }});
    llvm_return (llvm_term {{ 1 + x + y : [32] }});
}) abc;
:::

which allows `x` to have any value on entry and includes a
specification of its resulting value afterwards.
One can also restrict the starting value of `x` if, for example, the
point of having it there is to keep track of how many calls to `f` and `g`
there have been and it's not supposed to exceed some limit.
Then later uses of these functions will need to require that the limit has
not yet been exceeded.

There is a fly in this ointment, however, which is that it is possible
for immutable globals to depend on mutable globals.
This does not work in SAW's model.
In particular, an immutable global initialized to the address of a mutable
global will not work correctly.

:::{code-block} c
int thingy_store;
int *const thingy = &thingy_store;
:::

Here `thingy` is a immutable pointer (what it points to cannot be
changed) that points to a mutable global.
The internal initialization of `thingy` will fail before the
specification can enable it with `llvm_alloc`.

To work around this problem, SAW has an experimental global allocation
mode.
After using `enable_experimental`, you can use one of these three
`TopLevel` functions to choose, before calling `llvm_verify`, how
LLVM globals are allocated:

- `llvm_alloc_constant_globals` specifies the default behavior, namely
  that immutable globals are automatically allocated and mutable
  globals are not.
  This is the safest mode and should be used unless one of the others is
  needed.

- `llvm_alloc_all_globals` specifies that *all* globals are to be automatically
  allocated, regardless of mutability.
  This will ensure that examples like the one above can be handled,
  but at the cost of expecting that the specification provide both
  pre-state and post-state for _all_ mutable globals.
  This is not fully checked and unsafe in general.
  See
  [Compositional Verification and Mutable Global Variables](#compositional-verification-and-mutable-global-variables)
  for discussion.

- `llvm_alloc_no_globals` disables all automatic initialization of globals.
  All allocation must be handled explicitly by the `LLVMSetup` block.
  This is in turn unsafe in the sense that immutable globals can be given
  arbitrary (and unrealizable) prestate values other than their actual
  initialization value, which then can lead to apparently successful
  verifications not grounded in reality.
  Always use `llvm_global_initializer` to generate the prestate values
  for immutable globals.
  For example:

  :::{code-block} sawscript
  llvm_points_to (llvm_global "thingy") (llvm_global_initializer "thingy");
  :::

Note that the value for a pointer like `thingy` in the above example,
but that is _not_ immutable (for example, might be set at program
startup to point to one of several possible globals), can be specified
with an assertion like the following:

:::{code-block} sawscript
llvm_points_to (llvm_global "thingy") (llvm_global "thingy_store");
:::

<!--
   ...which I mention because it took me a while to get it to work,
   and I theoretically know what I'm doing... it is easy to
   accidentally write a specification that doesn't capture the
   aliasing, which will then mostly be accepted.
   That's another way to get successful verifications not grounded in
   reality.
-->


### Assertions in the LLVM Backend

The basic function for LLVM assertions is `llvm_assert`.
It takes one argument, which is a `Term` (Cryptol-level value);
frequently that term will be a Cryptol block written with
double-braces.
If in the prestate logic, it generates a precondition; in the
poststate logic, it generates a postcondition.

The function `llvm_precond` is equivalent, except it is only
allowed in the prestate logic.
Similarly, `llvm_postcond` is only allowed in the poststate
logic.

The function `llvm_equal` is comparable to using `llvm_assert`
with an equality; it takes two arguments and asserts that
they are equal.
However, the arguments it takes are LLVM-level values
(`LLVMValue`) rather than Cryptol-level values (`Term`),
so it can express equalities that would be messy with
`llvm_assert`.
The use of `llvm_equal` when applicable can also sometimes lead to
more efficient symbolic execution.

The function `llvm_return` _`val`_ asserts that the value returned by
the function is _`val`_.
This is only allowed in the poststate logic.

The function `llvm_points_to` is the basic way to assert about
a pointer.
It takes two arguments that are both LLVM-level values; the
first is the pointer and the second is the contents.

There are some variants of `llvm_points_to`:

- `llvm_conditional_points_to` _`cond`_ _`ptr`_ _`val`_ asserts
  that the pointer _`ptr`_ points to the value _`val`_, but only
  when _`cond`_ is true.
  _`cond`_ is a Cryptol-level value of type `Term` that can be
  symbolic.

- `llvm_points_to_at_type` _`ptr`_ _`ty`_ _`val`_ casts the
  pointer _`ptr`_ to point at _`ty`_ before examining _`val`_.
  This can be used, for example, to read or write a prefix
  of an array.
  It can also be used in conjunction with C code that reinterprets
  the memory representation of one type in terms of another.
  One can also use `llvm_cast_pointer` instead.

- `llvm_conditional_points_to_at_type` _`cond`_ _`ptr`_ _`ty`_ _`val`_
  is both the previous functions rolled together.

- `llvm_points_to_untyped` _`ptr`_ _`val`_ and
  `llvm_conditional_points_to_untyped` _`cond`_ _`ptr`_ _`val`_
  disable typechecking of the pointer and value entirely.

- `llvm_points_to_array_prefix` _`ptr`_ _`arr`_ _`n`_ indicates
  that the pointer _`ptr`_ points to the first _`n`_ elements of
  _`arr`_.
  This is experimental.

### LLVM Bitfields

SAW has experimental support for specifying `struct`s with bitfields.
(The material below requires using `enable_experimental`.)

Consider the following example:

:::{code-block} c
struct s {
  uint8_t x:1;
  uint8_t y:1;
};
:::

Normally, a `struct` with two `uint8_t` fields would have an overall size of
two bytes. However, because the `x` and `y` fields are declared with bitfield
syntax, they are instead packed together into a single byte.

Because bitfields have somewhat unusual memory representations in LLVM, some
special care is required to write SAW specifications involving bitfields. For
this reason, there is a dedicated `llvm_points_to_bitfield` function for this
purpose:

- `llvm_points_to_bitfield : LLVMValue -> String -> LLVMValue -> LLVMSetup ()`

The type of `llvm_points_to_bitfield` is similar that of `llvm_points_to`,
except that it takes the name of a field within a bitfield as an additional
argument. For example, here is how to assert that the `y` field in the `struct`
example above should be `0`:

:::{code-block} sawscript
ss <- llvm_alloc (llvm_alias "struct.s");
llvm_points_to_bitfield ss "y" (llvm_term {{ 0 : [1] }});
:::

Note that the type of the right-hand side value (`0`, in this example) must
be a bitvector whose length is equal to the size of the field within the
bitfield. In this example, the `y` field was declared as `y:1`, so `y`'s value
must be of type `[1]`.

Note that the following specification is _not_ equivalent to the one above:

:::{code-block} sawscript
ss <- llvm_alloc (llvm_alias "struct.s");
llvm_points_to (llvm_field ss "y") (llvm_term {{ 0 : [1] }});
:::

`llvm_points_to` works quite differently from `llvm_points_to_bitfield` under
the hood, so using `llvm_points_to` on bitfields will almost certainly not work
as expected.

In order to use `llvm_points_to_bitfield`, one must also use the
`enable_lax_loads_and_stores` command:

- `enable_lax_loads_and_stores: TopLevel ()`

The `enable_lax_loads_and_stores` command relaxes some
of SAW's assumptions about uninitialized memory, which is necessary to make
`llvm_points_to_bitfield` work under the hood. For example, reading from
uninitialized memory normally results in an error in SAW, but with
`enable_lax_loads_and_stores`, such a read will instead return a symbolic
value. At present, `enable_lax_loads_and_stores` only works with What4-based
tactics (e.g., `w4_unint_z3`); using it with SBV-based tactics
(e.g., `sbv_unint_z3`) will result in an error.

Note that SAW relies on LLVM debug metadata in order to determine which struct
fields reside within a bitfield. As a result, you must pass `-g` to `clang` when
compiling code involving bitfields in order for SAW to be able to reason about
them.

### Loading LLVM Modules

To load LLVM code, simply provide the location of a valid bitcode file
to the `llvm_load_module` function.

- `llvm_load_module : String -> TopLevel LLVMModule`

The resulting module handle can be passed to `llvm_verify` and similar functions.

The LLVM bitcode parser should generally work with LLVM versions between
3.5 and 21, though it may be incomplete for some versions. Debug
metadata has changed somewhat throughout that version range, so is the
most likely case of incompleteness. We aim to support every version
after 3.5, however, so report any parsing failures as [issues on
GitHub](https://github.com/GaloisInc/saw-script/issues).

#### Tips on Compiling LLVM

For generating LLVM with `clang`, it can be helpful to:

- Turn on debugging symbols with `-g` so that SAW can find source
  locations of functions, names of variables, etc.

- Optimize with `-O1` so that the generated bitcode more closely matches
  the C/C++ source, making the results more comprehensible.

- Use `-fno-threadsafe-statics` to prevent `clang` from emitting
  unnecessary pthread code.

- Link all relevant bitcode with `llvm-link` (including, e.g., the C++
  standard library when analyzing C++ code).

All SAW proofs include side conditions to rule out undefined behavior,
and proofs will only succeed if all of these side conditions have been
discharged. However the default SAW notion of undefined behavior is with
respect to the semantics of LLVM, rather than C or C++. If you want to
rule out undefined behavior according to the C or C++ standards,
consider compiling your code with `-fsanitize=undefined` or one of the
related flags[^1] to `clang`.

Generally, you'll also want to use `-fsanitize-trap=undefined`, or one
of the related flags, to cause the compiled code to use `llvm.trap` to
indicate the presence of undefined behavior. Otherwise, the compiled
code will call a separate function, such as
`__ubsan_handle_shift_out_of_bounds`, for each type of undefined
behavior, and SAW currently does not have built in support for these
functions (though you could manually create overrides for them in a
verification script).

[^1]: <https://clang.llvm.org/docs/UsersManual.html#controlling-code-generation>

#### Working With C++

The distance between C++ code and LLVM is greater than between C and
LLVM, so some additional considerations come into play when analyzing
C++ code with SAW.

The first key issue is that the C++ standard library is large and
complex, and tends to be widely used by C++ applications. To analyze
most C++ code, it will be necessary to link your code with a version of
the `libc++` library[^2] compiled to LLVM bitcode. The `wllvm` program[^3]
can be useful for this.

The C++ standard library includes a number of key global variables, and
any code that touches them will require that they be initialized using
`llvm_alloc_global`.

Many C++ names are slightly awkward to deal with in SAW. They may be
mangled relative to the text that appears in the C++ source code. SAW
currently only understands the mangled names. The `llvm-nm` program can
be used to show the list of symbols in an LLVM bitcode file, and the
`c++filt` program can be used to demangle them, which can help in
identifying the symbol you want to refer to. In addition, C++ names from
namespaces can sometimes include quote marks in their LLVM encoding. For
example:

:::{code-block} llvm
%"class.quux::Foo" = type { i32, i32 }
:::

This can be mentioned in SAW by saying:

:::{code-block} sawscript
llvm_type "%\"class.quux::Foo\""
:::

Finally, there is no support for calling constructors in specifications,
so you will need to construct objects piece-by-piece using, e.g.,
`llvm_alloc` and `llvm_points_to`.

[^2]: <https://libcxx.llvm.org/index.html>
[^3]: <https://github.com/travitch/whole-program-llvm>

#### Multiple LLVM Bitcode Files

If you have multiple bitcode modules, you can join them together
before loading using the `llvm-link` utility.

Alternatively, you can load them each independently with a separate
`llvm_load_module` command and then combine them with the
`llvm_combine_modules` function.

`llvm_combine_modules` _`main`_ _`others`_ links the modules in
_`others`_ to the module _`main`_ and returns (in `TopLevel`) a new
LLVM module handle.
It is by no means a full-blown linker implementation and should only
be used with groups of modules that were meant to be linked together.
The modules should be listed in order from caller to callee, the same
as on the command line of a Unix linker.
If duplicate names appear, names in earlier modules will shadow names
in later modules.


### LLVM Verification

Verification of LLVM is done with the `llvm_verify` command.

:::{code-block} sawscript
llvm_verify :
  LLVMModule ->
  String ->
  [LLVMSpec] ->
  Bool ->
  LLVMSetup () ->
  ProofScript () ->
  TopLevel LLVMSpec
:::

The first two arguments specify the module and function name to verify.
The third argument specifies the list of already-verified
specifications to use as overrides for compositional verification.
The fourth argument specifies
whether to do path satisfiability checking, and the fifth gives the
specification of the function to be verified. Finally, the last argument
gives the proof script to use for verification. The result is a proved
specification that can be used to simplify verification of functions
that call this one.


<!-- ------------------------------------------------------------ -->


## The JVM Backend and JVM Specifications

In the JVM backend, types appear as values of SAWSCript type
`JavaType` (not `JVMType`, by historical accident), and values have
the type `JVMValue`.
JVM code modules are class files and thus have the type `JavaClass`.
JVM specification do-blocks have the type `JVMSetup ()`.

The function argument declaration that divides the pre- and post-
portions of a specification is done with `jvm_execute_func`.

(jvm-types)=
### JVM Types

JVM types appear in SAWScript as values of type `JVMType`.
The following SAWScript functions construct JVM types:

- `java_bool` is the Java `bool` type.
  This corresponds to the Cryptol `Bit` or `Bool` type.
  Lifting a Cryptol `Bit` value with `jvm_term` produces a Java `bool`.

- `java_byte` is the Java `byte` type, which is an 8-bit bitvector.
  This corresponds to the Cryptol `[8]` type.

- `java_char` is the Java `char` type, which is a 16-bit bitvector.
  (Recall that Java is stuck with UTF-16 strings for legacy reasons.)
  This corresponds to the Cryptol `[16]` type.

- `java_short` is the Java `short` type, which is also a 16-bit bitvector.
  This corresponds to the Cryptol `[16]` type.
  <!-- XXX: which do you get if you jvm_term a [16]? -->

- `java_int` is the Java `int` type, which is a 32-bit bitvector.
  This corresponds to the Cryptol `[32]` type.

- `java_long` is the Java `long` type, which is a 64-bit bitvector.
  This corresponds to the Cryptol `[64]` type.

- `java_float` and `java_double` are the Java `float` and `double`
  types, which are 32-bit and 64-bit floating point numbers
  respectively.
  These correspond to the Cryptol floating point types of the proper
  size.
  However, SAW's support for floating point is rudimentary so these
  types are currently of little use.

- `java_array` _`n`_ _`ty`_ is an array of length _`n`_ and element type
  _`ty`_.
  This type corresponds to the Cryptol sequence type `[`_`n`_`][`_`cty`_`]`
  where _`cty`_ is the Cryptol type corresponding to _`ty`_, assuming
  there is one.
  Lifting a Cryptol sequence value to a JVM value produces a value
  of this type.
  (Note that Cryptol bitvectors are also sequences.
  A Cryptol sequence of `Bit` / `Bool` is a bitvector and lifts to
  a Java integer type if one of the right size exists.
  Otherwise it fails.
  A Cryptol sequence of some other type lifts to an `java_array`.)

- `java_class` _`cl`_ is the type of the Java class called _`cl`_.
  This does not correspond to any Cryptol type.

It is not possible to generate a Java array of `bool` with `jvm_term`
and a Cryptol value; a Cryptol sequence of `Bit` will produce a
machine integer type instead.
As a workaround one can allocate a fresh array with `jvm_alloc_array`
and assert about its elements individually.
Allocation is discussed below in the next section.

### JVM Values and Allocation

The primary way to produce JVM values of base type is to lift
Cryptol values with `jvm_term`.
For example, `jvm_term {{ 123 : [32] }}` produces a JVM value
whose type is `java_int`.

All compound values in Java are instances or arrays, and all
class instance or array values are pointers/references.
This allows a simpler interface than in the LLVM and MIR backends:
instances and arrays are allocated, and then one can assert
directly about their fields and elements.
There is no need to materialize instance or array values directly.

- `jvm_alloc_object` _`cl`_ allocates an object instance of type
  _`cl`_.

- `jvm_alloc_array` _`n`_ _`ty`_ allocates an array of _`n`_ elements
   of type _`ty`_.

These functions return `JVMValue` values whose JVM-level type is
`java_class` _`cl`_ and `java_array` _`n`_ _`ty`_ respectively.
As in the Java language, these are implicitly pointers/references,
and there are no explicit pointers or references needed.

Instances or arrays allocated in the prestate logic are presumed to
exist before the function is called; those allocated (in the
`jvm_alloc_object` sense) in the poststate logic are expected to be
allocated (in the `new` runtime sense) by the function.

The Java null pointer is called `jvm_null`.

### Binding Quantified JVM Values

The basic function in the JVM backend is `jvm_fresh_var` _`x`_
_`ty`_.
_`x`_ is a string, which provides an internal name for the
variable, and _`ty`_ is the type to generate.
This type is a JVM-level type, not a Cryptol type.
However, it must be a JVM type that has a corresponding Cryptol type,
because the result is a Cryptol-level value of type `Term`.

For example:

```sawscript
x <- jvm_fresh_var "x" java_int;
```

This produces a fresh 32-bit machine integer.

It is reasonable to use the same identifier for the internal name and
for the SAWScript variable, and, where applicable, to make it the same
name as used for the same thing in the code under verification.

<!--
   XXX: currently it's possible to use the same internal name for
   multiple variables. This is a consequence of #3060 and not
   something we want to advertise.
-->

### JVM Static Variables

In the JVM backend, static values always exist and can be reasoned
about with `jvm_static_field_is`.

There are some unresolved questions about initialization for static
values; see
[issue #916](https://github.com/GaloisInc/saw-script/issues/916).

### JVM Assertions

The basic function for JVM assertions is `jvm_assert`.
It takes one argument, which is a `Term` (Cryptol-level value);
frequently that term will be a Cryptol block written with
double-braces.
If in the prestate logic, it generates a precondition; in the
poststate logic, it generates a postcondition.

The function `jvm_precond` is equivalent, except it is only
allowed in the prestate logic.
Similarly, `jvm_postcond` is only allowed in the poststate
logic.

The function `jvm_equal` is comparable to using `jvm_assert`
with an equality; it takes two arguments and asserts that
they are equal.
However, the arguments it takes are JVM-level values
(`JVMValue`) rather than Cryptol-level values (`Term`),
so it can express equalities that would be messy with
`jvm_assert`.
The use of `jvm_equal` when applicable can also sometimes lead to
more efficient symbolic execution.

The function `jvm_return` _`val`_ asserts that the value returned by
the function is _`val`_.
This is only allowed in the poststate logic.

The following functions are used for reasoning about the
values of class instance and array elements:

- `jvm_field_is` _`obj`_ _`f`_ _`val`_ asserts that field _`f`_
  of an object value _`obj`_ has value _`val`_.
  _`val`_ is a JVM-level value.

- `jvm_static_field_is` _`f`_ _`val`_ asserts that the static field _`f`_
  (which may be qualified with a class name) has value _`val`_.
  _`val`_ is a JVM-level value.
  If no class name is included, the class of the method being verified is
  assumed.

- `jvm_elem_is` _`arr`_ _`n`_ _`val`_ asserts that the element _`n`_
  of the array _`arr`_ has the value _`val`_.
  _`val`_ is a JVM-level value.

- `jvm_array_is` _`arr`_ _`val`_ asserts that the array _`arr`_ has the
  contents _`val`_, which is a _Cryptol_-level value of sequence type.

There are variant versions of each of these that do not take a value;
instead they implicitly create a fresh value.
These are convenient when the value produced is not specified or
indeterminate/unpredictable.
They can also be used to write partial specifications when detailed
reasoning about the output value isn't currently necessary.

- `jvm_modifies_field` _`obj`_ _`f`_
- `jvm_modifies_static_field` _`f`_
- `jvm_modifies_elem` _`arr`_ _`n`_
- `jvm_modifies_array` _`arr`_

<!--
   XXX: is `jvm_modifies_array` equivalent to `jvm_modifies_elem` on all
   its elements, or does it also apply havoc to the array size?
-->

### Loading JVM Code

Loading Java code is more complex than with the other backends, because
of the more structured nature of Java packages.
When running `saw`, three command-line options control where to look for classes:

- The `-b` flag takes the path where the `java` executable lives, which is used
  to locate the Java standard library classes and add them to the class
  database. Alternatively, one can put the directory where `java` lives
 [on the `PATH`](path-definition), which SAW will search if `-b` is not set.

- The `-j` flag takes the name of a JAR file as an argument and adds the
  contents of that file to the class database.

- The `-c` flag takes the name of a directory as an argument and adds all class
  files found in that directory (and its subdirectories) to the class database.
  By default, the current directory is included in the class path.

Most Java programs will only require setting the `-b` flag (or the `PATH`), as
that is enough to bring in the standard Java libraries. Note that when
searching the `PATH`, SAW makes assumptions about where the standard library
classes live. These assumptions are likely to hold on JDK 7 or later, but they
may not hold on older JDKs on certain operating systems. If you are using an
old version of the JDK and SAW is unable to find a standard Java class, you may
need to specify the location of the standard classes' JAR file with the `-j`
flag (or, alternatively, with the `SAW_JDK_JAR` environment variable).

Once the class path is configured, you can pass the name of a class to
the `java_load_class` function.

- `java_load_class : String -> TopLevel JavaClass`

The resulting `JavaClass` can be passed to `jvm_verify` and related
functions.

Java class files from any JDK newer than version 6 should work. However,
support for JDK 9 and later is experimental. Verifying code that only uses
primitive data types is known to work well, but there are some as-of-yet
unresolved issues in verifying code involving classes such as `String`. For
more information on these issues, refer to
[this GitHub issue](https://github.com/GaloisInc/crucible/issues/641).

For Java, the only compilation flag that tends to be valuable is `-g` to
retain information about the names of function arguments and local
variables.

### JVM Verification

Verification of JVM byte code is done with the `jvm_verify` command.

:::{code-block} sawscript
jvm_verify :
  JavaClass ->
  String ->
  [JVMSpec] ->
  Bool ->
  JVMSetup () ->
  ProofScript () ->
  TopLevel JVMSpec
:::

The first two arguments specify the class and method name to verify.
The third argument specifies the list of already-verified
specifications to use as overrides for compositional verification.
The fourth argument specifies
whether to do path satisfiability checking, and the fifth gives the
specification of the function to be verified. Finally, the last argument
gives the proof script to use for verification. The result is a proved
specification that can be used to simplify verification of functions
that call this one.


<!-- ------------------------------------------------------------ -->


## The MIR backend and Rust/MIR Specifications

In the MIR backend, types appear as values of SAWScript type
`MIRType`.
There are also separate handles for Rust algebraic data types,
which appear as SAWScript type `MIRAdt`.
Values have the type `MIRValue`; code modules have the type `MIRModule`;
and specification do-blocks have the type `MIRSetup ()`.

The function argument declaration that divides the pre- and post-
portions of a specification is done with `mir_execute_func`.

(mir-types)=
### MIR (Rust) Types

The following SAWScript functions construct MIR types:

- `mir_bool` is the Rust `bool` type.
  This corresponds to the Cryptol `Bit` or `Bool` type.
  Lifting a Cryptol `Bit` value with `mir_term` produces a Rust `bool`.

- `mir_char` is the Rust `char` type.
  It corresponds to the Cryptol `[32]` type.
  <!-- XXX what do you get if you lift a [32] with mir_term? -->

- `mir_i8` and `mir_u8` are the Rust `i8` and `u8` types respectively.
  These are 8-bit bitvectors and (both) correspond to the Cryptol `[8]` type.

- `mir_i16` and `mir_u16` are the Rust `i16` and `u16` types respectively.
  These are 16-bit bitvectors and (both) correspond to the Cryptol `[16]` type.

- `mir_i32` and `mir_u32` are the Rust `i32` and `u32` types respectively.
  These are 32-bit bitvectors and (both) correspond to the Cryptol `[32]` type.

- `mir_i64` and `mir_u64` are the Rust `i64` and `u64` types respectively.
  These are 64-bit bitvectors and (both) correspond to the Cryptol `[64]` type.

- `mir_i128` and `mir_u128` are the Rust `i128` and `u128` types respectively.
  These are 128-bit bitvectors and (both) correspond to the Cryptol `[128]` type.

- `mir_isize` and `mir_usize` are the Rust `isize` and `usize` types respectively.
  These are pointer-sized bitvectors and, in SAW, both correspond to the
  Cryptol `[64]` type.
  For the time being, SAW treats all Rust code as 64-bit.

- `mir_f32` is the type of Rust single-precision floating point values.
  This corresponds to the Cryptol floating point type of the proper
  size.
  However, SAW's support for floating point is rudimentary so this
  type is of little use currently.

- `mir_f64` is the type of Rust double-precision floating point values.
  This corresponds to the Cryptol floating point type of the proper
  size.
  However, SAW's support for floating point is rudimentary so this
  type is of little use currently.

- `mir_tuple` _`tys`_ is the type of a Rust tuple containing the types _`tys`_,
  in order.
  This corresponds to the Cryptol tuple type containing the corresponding
  Cryptol types, if they exist.
  <!-- XXX: What about tuple-structs? -->

- `mir_array` _`n`_ _`ty`_ is the type of an array of element type _`ty`_
  that is _`n`_ entries long.
  This type corresponds to the Cryptol sequence type `[`_`n`_`][`_`cty`_`]`
  where _`cty`_ is the Cryptol type corresponding to _`ty`_, if it exists.

- `mir_adt` _`adt`_ is the type of a Rust algebraic data type.
  The _`adt`_ argument is a value of type `MIRAdt`, which can be looked up
  in a loaded MIR module by name.
  The `MIRAdt` type is a layer of indirection that makes ADT operations
  on non-ADT types ill-typed in SAWScript, which helps avoid various
  mistakes.
  Rust ADTs have no corresponding Cryptol type.

- `mir_ref` _`ty`_ is the type of immutable references to _`ty`_.
  It has no corresponding Cryptol type.

- `mir_ref_mut` _`ty`_ is the type of mutable references to _`ty`_.
  It has no corresponding Cryptol type.

- `mir_raw_pointer_const` _`ty`_ is the type of immutable raw pointers to _`ty`_.
  It has no corresponding Cryptol type.

- `mir_raw_pointer_mut` _`ty`_ is the type of mutable raw pointers to _`ty`_.
  It has no corresponding Cryptol type.

- `mir_slice` _`ty`_ is the type of a (reference to a) Rust slice of
  element type _`ty`_.
  Currently SAW can only handle references to slices: `&[`_`ty`_`]` in
  Rust terms.
  This has no corresponding Cryptol type.

- `mir_str` is the type of a (reference to a) Rust string slice.
  Currently SAW can only handle references to strings: `&str` in
  Rust terms.
  This has no corresponding Cryptol type.

- `mir_vec` _`mod`_ _`ty`_ is the type of a Rust vector of element
  type _`ty`_: `Vec<`_`ty`_`>` in Rust terms.
  _`mod`_ is a handle for a MIR code module (see below) that is needed
  to look up some internal identifiers.

Lifting Cryptol bitvector values produces the corresponding sized
Rust/MIR integer types; however, whether it is the signed or unsigned
version is unspecified.
Typechecking at the MIR/Rust level is relaxed so that the signed and
unsigned versions are considered equivalent.
<!--
   XXX: do we also allow mixing `i64`/`u64` with `isize`/`usize`?
   I'd expect so.
-->

Also, it is not possible to generate a MIR array of `bool` with
`mir_term` and a Cryptol value; a Cryptol sequence of `Bit` will
produce a machine integer type instead.
As a workaround one can create a fresh array value with
`mir_fresh_expanded_value` (described below) and assert about its
elements individually.

### MIR Values

The primary way to produce MIR values of base type is to lift
Cryptol values with `mir_term`.
For example, `mir_term {{ 123 : [32] }}` produces a MIR value
whose type is `mir_i32`.

MIR values of compound type are produced with the following functions:

- `mir_enum_value` _`adt`_ _`name`_ _`args`_ produces a MIR value
  whose type is a Rust/MIR enumerated type / algebraic data type.
  _`adt`_ is the type; ADTs can be retrieved using `mir_find_adt`.
  _`name`_ is a string; it is the constructor name for the desired
  variant.
  This should be the short form of the name within the type, such
  as `"None"`; it does not need to be a fully-qualified identifier.
  _`args`_ is a list of MIR-level values to use as the arguments
  to the data constructor.
  Note that `mir_enum_value` can only be used to construct a single
  specific variant. If you need to construct a symbolic enum value
  that can range over many potential variants, use
  `mir_fresh_expanded_value` instead.

- `mir_tuple_value` _`elems`_ produces a MIR tuple value.
  _`elems`_ provides the contents of (and defines the arity of) the tuple.

- `mir_array_value` _`ty`_ _`elems`_ produces a MIR array value.
  _`ty`_ is the element type; _`elems`_ is a list of values to populate
  the array with.
  The type must match the element list... unless the element list is
  empty.

- `mir_struct_value` _`adt`_ _`vals`_ produces a MIR struct value.
  _`adt`_ gives the type (as with `mir_enum_value`, use `mir_find_adt`
  to look up the type handle) and _`vals`_ gives values for the fields,
  in order.

- `mir_slice_value` _`arr`_ generates a slice value from an array reference.
  The slice contains the whole array.
  This is equivalent to `&`_`arr`_`[..]` in Rust.
  The argument must be an allocated array reference (not an array value)
  whose Rust type is `&[`_`ty`_; _`n`_`]` or `&mut [`_`ty`_; _`n`_`]`.
  The resulting slice is immutable (`&[`_`ty`_`]`) or mutable (`&mut [`_`ty`_`]`)
  depending on the mutability of the base reference.

- `mir_slice_range_value` _`arr`_ _`lo`_ _`hi`_ is like `mir_slice_value` but
  generates a slice that refers to a subrange of the array; i.e.
  `&`_`arr`_`[`_`lo`_`..`_`hi`_`]`.
  It includes the elements from index _`lo`_ up to but not including
  index _`hi`_.
  It is an error for _`lo`_ to exceed _`hi`_ or for either to index
  past the end of the underlying array.
  Also note that the index arguments have the SAWScript type `Int`, that is,
  they are constants.
  It is not possible to create a slice with a symbolic length.
  If this limitation prevents you from using SAW, please file an issue
  [on GitHub](https://github.com/GaloisInc/saw-script/issues).

- `mir_str_slice_value` _`arr`_ creates a string slice (of Rust type
  `&str`) from an array reference whose element type is `u8`.
  It is otherwise the same as `mir_slice_value`.
  The array is expected to be a UTF-8-encoded sequence of bytes.

- `mir_str_slice_range_value` _`arr`_ _`lo`_ _`hi`_ has the same
  relationship to `mir_str_slice_value` that `mir_slice_range_value`
  has to `mir_slice_value`.

The elements of MIR values of compound type can be extracted with these
functions:

- `mir_elem_value` _`arr`_ _`ix`_ takes an array value and an index,
  and returns the value in the array at that index.
  This returns a MIR-level value (type `MIRValue`).

- `mir_elem_ref` _`arr`_ _`ix`_ is like `mir_elem_value`, but takes a
  reference (or a raw pointer) to an array and returns a reference
  (or, respectively, a raw pointer) to the element in the array.
  The reference or raw pointer must already point to an array value.
  (Unlike the analogous `llvm_elem`, `mir_elem_ref` cannot be used to
  initialize freshly-allocated memory.)

  <!-- XXX do these work on slices? -->

- `mir_field_value` _`str`_ _`f`_ takes a struct value _`str`_ and a
  field name _`f`_, which should be a string, and returns the value of
  the field.
  For "tuple structs" with numbered fields, use a string containing an
  integer constant, such as `"1"`.

- `mir_field_ref` _`str`_ _`f`_ is like `mir_field_value`, but takes a
  reference (or a raw pointer) instead of an immediate struct value
  and returns a reference (or, respectively, a raw pointer) to the
  named field.
  The reference or raw pointer must already point to a struct value.
  (Unlike the analogous `llvm_elem` or `llvm_field`, `mir_field_ref`
  cannot be used to initialize freshly-allocated memory.)

It is also possible to create an if-then-else expression at the MIR
value level using the function `mir_mux_values`.
It takes three arguments: the first is a Cryptol-level `Term` whose
underlying type should be boolean, and the second and third are
MIR-level values to produce if the control value is true and false
respectively.
The control value may be symbolic.

<!--
   We previously had this example of `mir_enum_value`, which I think
   is not needed, and would be difficult to wedge in above, but I'm
   not prepared to throw away quite yet.
   

Here is an example of using `mir_enum_value` in practice:

:::{code-block} rust
pub fn n() -> Option<u32> {
    None
}

pub fn s(x: u32) -> Option<u32> {
    Some(x)
}
:::

:::{code-block} sawscript
m <- mir_load_module "example.linked-mir.json";

let option_u32 = mir_find_adt m "core::option::Option" [mir_u32];

let n_spec = do {
  mir_execute_func [];

  mir_return (mir_enum_value option_u32 "None" []);
};

let s_spec = do {
  x <- mir_fresh_var "x" mir_u32;

  mir_execute_func [mir_term x];

  mir_return (mir_enum_value option_u32 "Some" [mir_term x]);
};
:::

-->

### Slice Example

Consider this Rust function, which accepts an arbitrary slice as an
argument:

:::{code-block} rust
pub fn f(s: &[u32]) -> u32 {
    s[0] + s[1]
}
:::

We can write a specification that passes a slice to the array `[1, 2, 3, 4, 5]`
as an argument to `f`:

:::{code-block} sawscript
let f_spec_1 = do {
  a <- mir_alloc (mir_array 5 mir_u32);
  mir_points_to a (mir_term {{ [1, 2, 3, 4, 5] : [5][32] }});

  mir_execute_func [mir_slice_value a];

  mir_return (mir_term {{ 3 : [32] }});
};
:::

Alternatively, we can write a specification that passes a part of this array
over the range `[1..3]`, i.e., ranging from second element to the fourth.
Because this is a half-open range, the resulting slice has length 2:

:::{code-block} sawscript
let f_spec_2 = do {
  a <- mir_alloc (mir_array 5 mir_u32);
  mir_points_to a (mir_term {{ [1, 2, 3, 4, 5] : [5][32] }});

  mir_execute_func [mir_slice_range_value a 1 3];

  mir_return (mir_term {{ 5 : [32] }});
};
:::

Note that we are passing _references_ to arrays to `mir_slice_value` and
`mir_slice_range_value`. It would be an error to pass a bare array to these
functions, so the following specification would be invalid:

:::{code-block} sawscript
let f_fail_spec = do {
  let arr = mir_term {{ [1, 2, 3, 4, 5] : [5][32] }};

  mir_execute_func [mir_slice_value arr]; // BAD: `arr` is not a reference

  mir_return (mir_term {{ 3 : [32] }});
};
:::

### Notes on Strings

One unusual requirement about `mir_str_slice_value` and
`mir_str_slice_range_value` is that they require the argument to be of type
`&[u8; N]`, i.e., a reference to an array of bytes. This is an artifact of the
way that strings are encoded in Cryptol. The following Cryptol expressions:

- `"A"`
- `"123"`
- `"Hello World"`

have the following types:

- `[1][8]`
- `[3][8]`
- `[11][8]`

This is because Cryptol strings are syntactic shorthand for sequences of bytes.
The following Cryptol expressions are wholly equivalent to the string literals
above:

- `[0x41]`
- `[0x31, 0x32, 0x33]`
- `[0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x57, 0x6f, 0x72, 0x6c, 0x64]`

These represent the strings in the extended ASCII character encoding. The
Cryptol sequence type `[N][8]` corresponds to the Rust type `[u8; N]`, so the
requirement to have something of type `&[u8; N]` as an argument reflects this
design choice.

Note that `mir_str_slice_value` and `mir_slice_value` applied to the same
`u8` array reference are _not_ the same thing.
The two commands represent different types
of Rust values. While both commands take the same argument type,
`mir_str_slice_value` will return a value of Rust type `&str` (or `&mut str`),
whereas `mir_slice_value` will return a value of Rust type `&[u8]` (or `&mut
[u8]`). These Rust types are checked when you pass these values as arguments to
Rust functions (using `mir_execute_func`) or when you return these values
(using `mir_return`), and it is an error to supply a `&str` value in a place
where a `&[u8]` value is expected (and vice versa).

As an example of how to write specifications involving string slices,
consider this Rust function:

:::{code-block} rust
pub fn my_len(s: &str) -> usize {
    s.len()
}
:::

We can use `mir_str_slice_value` to write a specification for `my_len` when it
is given the string `"hello"` as an argument:

:::{code-block} sawscript
let my_len_spec = do {
  s <- mir_alloc (mir_array 5 mir_u8);
  mir_points_to s (mir_term {{ "hello" }});

  mir_execute_func [mir_str_slice_value s];

  mir_return (mir_term {{ 5 : [64] }});
};
:::

Currently, Cryptol only supports characters that can be encoded in a single
byte. As a result, it is not currently possible to take slices of strings with
certain characters. For example, the string `"roșu"` cannot be used as a
Cryptol expression, as the character `'ș'` would require 10 bits to represent
instead of 8. The alternative is to use UTF-8 to encode such characters. For
instance, the UTF-8 encoding of the string `"roșu"` is `"ro\200\153u"`, where
`"\200\153"` is a sequence of two bytes that represents the `'ș'` character.

SAW makes no attempt to ensure that string slices over a particular range
aligns with UTF-8 character boundaries. For example, the following Rust code
would panic:

:::{code-block} rust
    let rosu: &str = "roșu";
    let s: &str = &rosu[0..3];
    println!("{:?}", s);
:::

:::{code-block} console
thread 'main' panicked at 'byte index 3 is not a char boundary; it is inside 'ș' (bytes 2..4) of `roșu`'
:::

On the other hand, SAW will allow you define a slice of the form
`mir_str_slice_range r 0 3`, where `r` is a reference to `"ro\200\153u"`. It is
the responsibility of the SAW user to ensure that `mir_str_slice_range` indices
align with character boundaries.

### Finding MIR Types

Rust supports a greater degree of polymorphism than the languages
behind the other backends; in particular Rust types can take
parameters.
This introduces various complications referring to type names.

We collectively refer to MIR `struct`s and `enum`s together as
_algebraic data types_, or ADTs for short.
The function `mir_find_adt` looks up a handle for an algebraic data
type by its name and type arguments for its type parameters.
It takes three arguments: the first is a MIR module handle, the
second is a string that names the type, and the third is a list of
type arguments.
The `MIRAdt` value returned can be given to the `mir_adt` function
to get a `MIRType`, or passed directly to the `mir_enum_value` and
`mir_struct_value` functions.

Alternatively, one can use the function `mir_find_mangled_adt` to
look up a particular instantiation of a type by its "mangled" name,
such as `foo::Bar::_adt12345`.
The code at the end corresponds to some particular set of type
arguments.
However, these codes are not stable (they change unpredictably at
the whim of `rustc`) and generally must be discovered by grovelling
manually in your `linked-mir.json` file.
Thus one should use `mir_find_adt` instead whenever possible.
`mir_find_mangled_adt` takes two arguments: a MIR module handle
and a string containing the mangled name.

For example, consider this code:

:::{code-block} rust
pub struct S<A, B> {
    pub x: A,
    pub y: B,
}

pub fn f() -> S<u8, u16> {
    S {
        x: 1,
        y: 2,
    }
}

pub fn g() -> S<u32, u64> {
    S {
        x: 3,
        y: 4,
    }
}
:::

At the MIR level, the return types of `f` and `g` are distinct types
each with their own names.
For example,

- `S<u8, u16>` might give rise to `example/abcd123::S::_adt456`
- `S<u32, u64>` might give rise to `example/abcd123::S::_adt789`

These can then be looked up with:

- `mir_find_adt m "example::S" [mir_u8,  mir_u16];`
- `mir_find_adt m "example::S" [mir_u32, mir_u64];`

or

- `mir_find_mangled_adt m "example::S::_adt456";`
- `mir_find_mangled_adt m "example::S::_adt789";`

but in the second case one must discover the codes `456` and `789`.

The lookup functions return a SAWScript value of type `MIRAdt`, which
can then be used with `mir_adt` to get a `MIRType`, or with
`mir_struct_value` and `mir_enum_value` to construct MIR-level values.

#### Const Generics

Rust ADTs can have _const generic_ parameters that allow the ADT to be generic
over constant values.
For instance, the following Rust code declares a const generic parameter `N`
on the struct `S`, as well as on the functions `f` and `g` that compute `S`
values:

:::{code-block} rust
pub struct S<const N: usize> {
    pub x: [u32; N]
}

pub fn f(y: [u32; 1]) -> S<1> {
    S { x: y }
}

pub fn g(y: [u32; 2]) -> S<2> {
    S { x: y }
}
:::

Like with other forms of Rust generics, instantiating `S` with different
constants will give rise to different identifiers in the compiled MIR code.
SAW provides a `mir_const` function for specifying the values of constants
used to instantiate const generic parameters:

- `mir_const : MIRType -> Term -> MIRType`

For instance, in order to look up `S<1>`, use `mir_const` in conjunction with
`mir_find_adt` like so:

:::{code-block} sawscript
s_adt = mir_find_adt m "example::S" [mir_const mir_usize {{ 1 : [64] }}]
:::

Unlike other forms of `MIRType`s, the type returned by `mir_const` is not a
type that you can create values with.
For instance, calling `mir_alloc` or `mir_fresh_var` at a type returned by
`mir_const` will raise an error.
`mir_const` is only useful for looking up ADTs via `mir_find_adt`.

At present, `mir_const` only supports looking up constant values with the types
listed
[here](https://doc.rust-lang.org/1.86.0/reference/items/generics.html#r-items.generics.const.allowed-types)
in the Rust Reference.
Specifically, the `MIRType` argument must be one of the following, subject to
the following restrictions:

- A primitive integer type, i.e., `mir_u{8,16,32,64,128,size}` or
  `mir_i{8,16,32,64,128,size}`.
  The `Term` argument must be a bitvector of the corresponding size.
  For instance, if the `MIRType` is `mir_u8`, then the `Term` must be a
  bitvector of type `[8]`.

- `mir_bool`.
  The `Term` argument must be of type `Bit`.

- `mir_char`.
  The `Term` argument must be of type `[32]`.

### Finding MIR Values and Functions

Rust also supports polymorphic functions.
The Rust compiler does not generate a single generic implementation
for polymorphic functions; instead it generates a separate version for
every different type instantiation.
Like instantiated polymorphic types, these are distinguished by hash
codes, and the codes are not stable and not easy to discover.

The function `mir_find_name` looks up a function by its name and a
list of types used to instantiate its type parameters.
(The first argument is a string, the second is a list of `MIRType`.)
It returns the mangled name as a string.
This string can then be passed to `mir_verify` and other related
functions.

### Lifetime Values

Rust ADTs and functions can have _lifetime_ parameters as well as type
parameters.
The following Rust code declares a lifetime parameter `'a` on the
struct `S`, and also on the function `f` that computes an `S` value:

:::{code-block} rust
pub struct S<'a> {
    pub x: &'a u32,
}

pub fn f<'a>(y: &'a u32) -> S<'a> {
    S { x: y }
}
:::

When `mir-json` compiles a piece of Rust code that contains lifetime
parameters, it will instantiate all of the lifetime parameters with a
placeholder MIR type that is simply called `lifetime`. This is important to
keep in mind when looking up ADTs with `mir_find_adt`, as you will also need to
indicate to SAW that the lifetime parameter is instantiated with `lifetime`. In
order to do so, use `mir_lifetime`. For example, here is how to look up `S`
with `'a` instantiated to `lifetime`:

:::{code-block} sawscript
s_adt = mir_find_adt m "example::S" [mir_lifetime]
:::

Note that this part of SAW's design is subject to change in the future.
Ideally, users would not have to care about lifetimes at all at the MIR level;
see [this issue](https://github.com/GaloisInc/mir-json/issues/58) for further
discussion on this point. If that issue is fixed, then we will likely remove
`mir_lifetime`, as it will no longer be necessary.

### Binding Quantified MIR Variables

The basic function for this in the MIR backend is
`mir_fresh_var` _`x`_ _`ty`_.
_`x`_ provides an internal name for the variable; _`ty`_ gives its
type.
This type is a MIR type (a value of type `MIRType`) rather than
a Cryptol type.
However, it must be an MIR type that has a corresponding Cryptol
type, because the result is a Cryptol-level SAWScript value.
(Thus, it has type `Term` and not type `MIRValue`.)

For example:

```sawscript
x <- mir_fresh_var "x" mir_i32;
```

This produces a fresh 32-bit machine integer.

There is also an experimental function `mir_fresh_cryptol_var` that
takes a Cryptol type instead.

It is reasonable to use the same identifier for the internal name and
for the SAWScript variable, and, where applicable, to make it the same
name as used for the same thing in the code under verification.

The function `mir_fresh_expanded_value` _`name`_ _`ty`_ creates a
fresh value of MIR-level type (thus, the type argument is an
`MIRType`) and populates it recursively with fresh variables.
The _`name`_ argument is used as a prefix for the names of the
generated fresh variables.
This can be used for struct and array types.
However, types that are or contain references or raw pointers are not
currently supported.

In general, to reason about values of compound type, it is possible to
create fresh primitive values for the elements and create compound
values with functions like `mir_array_value`.
It is also possible to use `mir_fresh_expanded_value` and reason about
the contents by using functions like `mir_elem_value`.
Which is preferable is in most cases purely a matter of convenience.

### Allocation, References, and Pointers in the MIR Backend

MIR references and raw pointer values cannot be arbitrarily created;
one must in general explicitly allocate memory to create a reference
or pointer.
The reference or pointer so created can then be passed as a function
argument or used to initialize other values.
Pointers allocated in the prestate logic are presumed to exist before
the function is called; pointers allocated (in the `mir_alloc` sense)
in the poststate logic are expected to be allocated (in the runtime
sense) by the function.

The main allocator functions in the MIR backend are:

- `mir_alloc` _`ty`_ allocates an immutable reference.

- `mir_alloc_mut` _`ty`_ allocates a mutable reference.

Because Rust (and therefore MIR) distinguishes immutable references
from mutable references at the type level, it's important to use the
correct allocation function.

The allocation cannot be used to allocate slices (including string
slices).
Slices are shared references to other allocations; they can
be constructed directly using `mir_slice_value` and friends after
allocating the underlying reference.

There are also four functions for allocating raw pointers:

- `mir_alloc_raw_ptr_const` _`ty`_ allocates a constant raw pointer to _`ty`_:
  `*const` _`ty`_ in Rust terms.
- `mir_alloc_raw_ptr_mut` _`ty`_ allocates a mutable raw pointer to _`ty`_:
  `*mut` _`ty`_ in Rust terms.
- `mir_alloc_raw_ptr_const_multi` _`n`_ _`ty`_ allocates a constant raw pointer
  to a sequence/array of _`n`_ _`ty`_s.
- `mir_alloc_raw_ptr_mut_multi` _`n`_ _`ty`_ allocates a mutable raw pointer
  to a sequence/array of _`n`_ _`ty`_s.

In low-level (and unsafe) Rust code, it is possible to get a raw
pointer into an allocation of multiple values and do pointer
arithmetic, much like C arrays.
These pointers must be generated using the last two functions.
A pointer thus generated can be matched against a larger allocation;
a spec whose prestate allocates a multi-raw-pointer of length _`n`_ can be
used as an override spec in a context where the pointer is actually longer,
and a spec whose postate allocates a multi-raw-pointer of length _`n`_ will
verify even if the function allocates more space than that.
That is, these functions declare an allocation that contains at least _`n`_
values, and the actual allocation in the code can be larger.

Note that allocating memory and reasoning about its contents are
separate steps.
In most cases each `mir_alloc` should be paired with an `mir_points_to`
assertion (see below) that says something about the value found in the
allocated memory.
(Otherwise the memory is treated as uninitialized, and attempts to read
from it will be treated as an error.
This is sometimes necessary to model unsafe Rust code.)

The following convenience functions are also available.

- `mir_ref_of` _`val`_ and `mir_ref_of_mut` _`val`_ are convenience
  functions that combine `mir_alloc` (or `mir_alloc_mut`) with
  the `mir_points_to` assertion.

- `mir_vec_of` _`name`_ _`ty`_ _`vals`_ is an experimental convenience
  function that creates a value of type `Vec<`_`ty`_`>`.
  [`Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html) is a commonly used
  data type in the Rust standard library.
  The _`vals`_ argument is a `MIRValue` that's a MIR array (not a list
  of `MIRValue`s) used to populate the `Vec`.
  This can be created with `mir_array_value` or lifted from a Cryptol
  sequence value.
  The _`name`_ argument is used as a prefix for the names of the
  internal symbolic variables inside the `Vec`.
  (Effectively, it is the name of the symbolic `Vec` being built.)

  `Vec` is just a regular struct and not a special language construct, so
  technically no special SAW support is needed.
  However, you would need to explicitly specify all the internal details and
  invariants of `Vec`, and that can get quite messy.

  This function may change in the future; there are unresolved internal
  design questions.

There is a function `mir_cast_raw_ptr` that takes a raw pointer value
and a MIR type, and yields a new pointer value with an updated
pointed-to type.
This is an unsafe operation needed for handling certain kinds of
unsafe code.
The pointer cannot actually be accessed unless it is cast back to
its original type.
(It is thus different from `llvm_cast_pointer`, which allows
reinterpreting memory.)

(mir-static-items)=
### MIR Static Variables

Rust static values (global variables) can be referenced with the
function `mir_static` _`name`_, which returns a reference to the
static called _`name`_.
(The name follows the same qualification rules as other MIR names.)
This reference is mutable if and only if the static is mutable.
It can be reasoned about in the prestate and poststate logic like any
other reference.

The initialization value for a static can be fetched with
`mir_static_initializer` _`name`_.
Sometimes this will be the prestate value you want.

Explicit allocation like `llvm_alloc_global` is not required, even for
mutable statics.

Here is an example involving static items:

:::{code-block} rust
// statics.rs
static     S1: u8 = 1;
static mut S2: u8 = 2;

pub fn f() -> u8 {
    // Reading a mutable static item requires an `unsafe` block due to
    // aliasing and concurrency-related concerns. We have no aliasing,
    // and are only concerned about the behavior of this program in a
    // single-threaded context.
    let s2 = unsafe { S2 };
    S1 + s2
}
:::

We can write a specification for `f` like so:

:::{code-block} sawscript
// statics.saw

let f_spec = do {
  mir_points_to (mir_static "statics::S2")
                (mir_static_initializer "statics::S2");
  // Note that we do not need to initialize S1, as immutable static
  // items are implicitly initialized in every specification.

  mir_execute_func [];

  mir_return (mir_term {{ 3 : [8] }});
};

m <- mir_load_module "statics.linked-mir.json";

mir_verify m "statics::f" [] false f_spec z3;
:::

In order to use a specification involving mutable static items for
compositional verification, it is required to specify the value of all mutable
static items using the `mir_points_to` command in the specification's
postconditions.
For further explanation, see the
[Compositional Verification and Mutable Global Variables](#compositional-verification-and-mutable-global-variables)
section.

### Assertions in the MIR Backend

The basic function for MIR assertions is `mir_assert`.
It takes one argument, which is a `Term` (Cryptol-level value);
frequently that term will be a Cryptol block written with
double-braces.
If in the prestate logic, it generates a precondition; in the
poststate logic, it generates a postcondition.

The function `mir_precond` is equivalent, except it is only
allowed in the prestate logic.
Similarly, `mir_postcond` is only allowed in the poststate
logic.

The function `mir_equal` is comparable to using `mir_assert`
with an equality; it takes two arguments and asserts that
they are equal.
However, the arguments it takes are MIR-level values
(`MIRValue`) rather than Cryptol-level values (`Term`),
so it can express equalities that would be messy with
`mir_assert`.
The use of `mir_equal` when applicable can also sometimes lead to
more efficient symbolic execution.

The function `mir_return` _`val`_ asserts that the value returned by
the function is _`val`_.
This is only allowed in the poststate logic.

The function `mir_points_to` is the basic way to assert about
a pointer.
It takes two arguments that are both MIR-level values; the first is
the reference (or raw pointer) and the second is the contents.

There is a variant of `mir_points_to` for raw pointers that point at
sequences of values: `mir_points_to_multi`.
The first argument must be a raw pointer; the second should be a
`MIRValue` of array type.
The pointer must have been allocated with
`mir_alloc_raw_ptr_const_multi` or `mir_alloc_raw_ptr_mut_multi`
and should contain space for at least as many values as the
argument array holds.
The array is copied sequentially; it is not necessarily the case that
the pointed-to values are the contents of a Rust array.
Using a `MIRValue` allows lifting a Cryptol sequence with `mir_term`,
which is often convenient.

(loading-mir)=
### Loading MIR Modules

To load a piece of Rust code, first compile it to a MIR JSON file, as
described immediately below, and then provide the location of the JSON
file to the `mir_load_module` function:

- `mir_load_module : String -> TopLevel MIRModule`

SAW currently supports Rust code that can be built with a [September 14, 2025
Rust nightly](https://static.rust-lang.org/dist/2025-09-14/).  If you encounter
a Rust feature that SAW does not support, please report it [on
GitHub](https://github.com/GaloisInc/saw-script/issues).

(compiling-mir)=
#### Compiling MIR

When verifying Rust code, SAW processes Rust's MIR (mid-level intermediate
representation) language. In particular, SAW analyzes a particular form of MIR
that our [`mir-json`](https://github.com/GaloisInc/mir-json) tool produces. You
will need to install `mir-json` and run it on Rust code in order to produce MIR
JSON files that SAW can load.
You will also
need to use `mir-json` to build custom versions of the Rust standard libraries
that are more suited to verification purposes.

If you are working from a checkout of the `saw-script` repo, you can install
the `mir-json` tool and the custom Rust standard libraries by performing the
following steps:

1. Make sure you have the proper versions of the
   [`crucible`](https://github.com/GaloisInc/crucible) and `mir-json`
   submodules like so:

   :::{code-block} console
   $ git submodule update deps/crucible deps/mir-json
   :::

2. Navigate to the `mir-json` submodule:

   :::{code-block} console
   $ cd deps/mir-json
   :::

3. Follow the instructions laid out in the [`mir-json` installation
   instructions](https://github.com/GaloisInc/mir-json#installation-instructions)
   in order to install `mir-json`.

4. Run the `mir-json-translate-libs` script in the `mir-json` submodule:

   :::{code-block} console
   $ mir-json-translate-libs
   :::

   This will compile the custom versions of the Rust standard libraries using
   `mir-json`, placing the results under the `rlibs` subdirectory.

5. Finally, define a `SAW_RUST_LIBRARY_PATH` environment variable that points
   to the newly created `rlibs` subdirectory:

   :::{code-block} console
   $ export SAW_RUST_LIBRARY_PATH=<...>/mir-json/rlibs
   :::

For `cargo`-based projects, `mir-json` provides a `cargo` subcommand called
`cargo saw-build` that builds a JSON file suitable for use with SAW. `cargo
saw-build` integrates directly with `cargo`, so you can pass flags to it like
any other `cargo` subcommand. For example:

:::{code-block} console
# Make sure that SAW_RUST_LIBRARY_PATH is defined, as described above
$ cargo saw-build <other cargo flags>
<snip>
linking 11 mir files into <...>/example-364cf2df365c7055.linked-mir.json
<snip>
:::

Note that:

- The full output of `cargo saw-build` here is omitted. The important part is
  the `.linked-mir.json` file that appears after `linking X mir files into`, as
  that is the JSON file that must be loaded with SAW.
- `SAW_RUST_LIBRARY_PATH` should point to the MIR JSON files for the Rust
  standard library.

`mir-json` also supports compiling individual `.rs` files through `mir-json`'s
`saw-rustc` command. As the name suggests, it accepts all of the flags that
`rustc` accepts. For example:

:::{code-block} console
# Make sure that SAW_RUST_LIBRARY_PATH is defined, as described above
$ saw-rustc example.rs <other rustc flags>
<snip>
linking 11 mir files into <...>/example.linked-mir.json
<snip>
:::

### MIR Verification

Verification of Rust code in the MIR backend is done with the
`mir_verify` command.

:::{code-block} sawscript
mir_verify :
  MIRModule ->
  String ->
  [MIRSpec] ->
  Bool ->
  MIRSetup () ->
  ProofScript () ->
  TopLevel MIRSpec
:::

The first two arguments specify the module and function name to verify.
The third argument specifies the list of already-verified
specifications to use as overrides for compositional verification.
The fourth argument specifies
whether to do path satisfiability checking, and the fifth gives the
specification of the function to be verified. Finally, the last argument
gives the proof script to use for verification. The result is a proved
specification that can be used to simplify verification of functions
that call this one.

The `String` supplied as an argument to `mir_verify` is expected to be a
function _identifier_.
This should have one of the following forms:

- `<crate name>/<disambiguator>::<function path>`
- `<crate name>::<function path>`

Where:

- `<crate name>` is the name of the crate in which the function is defined. (If
  you produced your MIR JSON file by compiling a single `.rs` file with
  `saw-rustc`, then the crate name is the same as the name of the file, but
  without the `.rs` file extension.)
- `<disambiguator>` is a hash of the crate and its dependencies. In extreme
  cases, it is possible for two different crates to have identical crate names,
  in which case the disambiguator must be used to distinguish between the two
  crates. In the common case, however, most crate names will correspond to
  exactly one disambiguator, and you are allowed to leave out the
  `/<disambiguator>` part of the `String` in this case. If you supply an
  identifier with an ambiguous crate name and omit the disambiguator, then SAW
  will raise an error.
- `<function path>` is the path to the function within the crate. Sometimes,
  this is as simple as the function name itself. In other cases, a function
  path may involve multiple _segments_, depending on the module hierarchy for
  the program being verified. For instance, a `read` function located in
  `core/src/ptr/mod.rs` will have the identifier:

  :::{code-block} text
  core::ptr::read
  :::

  where `core` is the crate name and `ptr::read` is the function path, which
  has two segments `ptr` and `read`. There are also some special forms of
  segments that appear for functions defined in certain language constructs.
  For instance, if a function is defined in an `impl` block, then it will have
  `{impl}` as one of its segments, e.g.,

  :::{code-block} text
  core::ptr::const_ptr::{impl}::offset
  :::

  If you are in doubt about what the full identifier for a given function is,
  consult the MIR JSON file for your program.

  <!-- XXX which we should give some guidance about how to approach -->

  The Rust compiler generates a separate instance for each use of a polymorphic
  function at a different type.   These instances have a compiler-generated
  name, so (as discussed above) the easiest way to refer to them is by using the command
  `mir_find_name : MIRModule -> String -> [MIRType] -> String`.
  Given a Rust module, the name of a polymorphic function, and a list of types,
  `mir_find_name` will return the name of the corresponding instantiation.
  It fails if the polymorphic function or the given
  instantiation are not found.


<!-- ------------------------------------------------------------ -->


(compositional-verification)=
## Compositional Verification

As mentioned briefly above, SAW's specification scheme for code 
allows for compositional reasoning.
That is,
when proving properties of a given method or function, we can make use
of properties we have already proved about its callees rather than
analyzing them anew. This enables us to reason about much larger
and more complex systems than otherwise possible.

The `llvm_verify`, `jvm_verify`, and `mir_verify` functions return values of
type `LLVMSpec`, `JVMSpec`, and `MIRSpec`, respectively.
These values are opaque objects that internally contain both the information
provided in the associated `LLVMSetup`, `JVMSetup`, or `MIRSetup` specification do-blocks,
respectively, and the results of the verification process.

Any of these `Spec` objects can be passed in via the third
argument of the `..._verify` functions. For any function or method
specified by one of these parameters, the simulator will not follow
calls to the associated target. Instead, it will perform the following
steps:

- Check that all `llvm_points_to` and `llvm_precond` statements
  (or the corresponding JVM or MIR statements) in the specification are
  satisfied.

- Update the simulator state and optionally construct a return value as
  described in the specification.

More concretely, suppose we have an `add` function (simpler than the
one earlier in the chapter, which was supposed to also illustrate
memory allocation) and a doubling function written in terms of it:

:::{code-block} c
unsigned add(unsigned x, unsigned y) {
    return x + y;
}
unsigned dbl(unsigned *x) {
    return add(x, x);
}
:::

We can write a specification for `add`:

:::{code-block} sawscript
let add_spec = do {
   x <- llvm_fresh_var "x" (llvm_int 32);
   y <- llvm_fresh_var "y" (llvm_int 32);
   llvm_execute_func [llvm_term x, llvm_term y];
   llvm_return (llvm_term {{ x + y }});
};
:::

And one for `dbl`, which is very similar to the one for `add`:

:::{code-block} sawscript
let dbl_spec = do {
   x <- llvm_fresh_var "x" (llvm_int 32);
   llvm_execute_func [llvm_term x];
   llvm_return (llvm_term {{ x + x }});
};
:::

We can verify `add` and then verify `dbl` using what we proved about
`add`:

:::{code-block} sawscript
add_theorem <- llvm_verify bc "add" [] true add_spec z3;
dbl_theorem <- llvm_verify bc "dbl" [add_theorem] true dbl_spec z3;
:::

When `dbl` calls `add`, `llvm_verify` uses the specification we proved
instead of executing through it again.
In this case, it doesn't save computational effort, since `add` is so
simple.
However, it illustrates the approach.

Imagine we were doing something less trivial and `add` took
ten minutes to verify.
The compositional verification of `dbl` would, instead of taking another
ten minutes to verify, be almost instantaneous.

This example also illustrates a limitation of the technique: it only
allows reusing the _proof effort_.
The specification for `dbl` still needs to be a complete
characterization of its behavior, and you will notice it does not
share any logic with the specification for `add`.
Reusing _specification effort_ by sharing elements of the
specification is a different problem.
For logic more complicated than addition, one can factor out elements
of the behavioral specification into a shared Cryptol model.
(Sharing elements of the call setup and theorem statement requires
SAWScript programming, which is an advanced topic.
See [The SAWScript Language](#sawscript).)

#### Compositional Verification and Mutable Allocations

<!--
   XXX: I've left this discussion in for the time being, because it
   still describes the behavior of the system. However, the behavior
   is a bug: we consider leaving a value unspecified to mean different
   things in different contexts. As described below, when verifying a
   function, if a mutable value is left unspecified we interpret that
   to mean it can take on any value. But then when we go to use it as
   an override, we treat it as meaning the value is unchanged. This is
   inconsistent, and it's the inconsistency that's unsound, and at
   some point it should get fixed.
-->   

A common pitfall when using compositional verification is to reuse a
specification that underspecifies the value of a mutable allocation. In
general, doing so can lead to unsound verification, so SAW goes to great
length to check for this.

Here is an example of this pitfall in an LLVM verification. Given this C code:

:::{code-block} c
void side_effect(uint32_t *a) {
  *a = 0;
}

uint32_t foo(uint32_t x) {
  uint32_t b = x;
  side_effect(&b);
  return b;
}
:::

And the following SAW specifications:

:::{code-block} sawscript
let side_effect_spec = do {
  a_ptr <- llvm_alloc (llvm_int 32);
  a_val <- llvm_fresh_var "a_val" (llvm_int 32);
  llvm_points_to a_ptr (llvm_term a_val);

  llvm_execute_func [a_ptr];
};

let foo_spec = do {
  x <- llvm_fresh_var "x" (llvm_int 32);

  llvm_execute_func [llvm_term x];

  llvm_return (llvm_term x);
};
:::

Should SAW be able to verify the `foo` function against `foo_spec` using
compositional verification? That is, should the following be expected to work?

:::{code-block} sawscript
side_effect_ov <- llvm_verify m "side_effect" [] false side_effect_spec z3;
llvm_verify m "foo" [side_effect_ov] false foo_spec z3;
:::

A literal reading of `side_effect_spec` would suggest that the `side_effect`
function allocates `a_ptr` but then does nothing with it, implying that `foo`
returns its argument unchanged. This is incorrect, however, as the
`side_effect` function actually changes its argument to point to `0`, so the
`foo` function ought to return `0` as a result. SAW should not verify `foo`
against `foo_spec`, and indeed it does not.

The problem is that `side_effect_spec` underspecifies the value of `a_ptr` in
its postconditions, which can lead to the potential unsoundness seen above when
`side_effect_spec` is used in compositional verification. To prevent this
source of unsoundness, SAW will _invalidate_ the underlying memory of any
mutable pointers (i.e., those declared with `llvm_alloc`, not
`llvm_alloc_global`) allocated in the preconditions of compositional override
that do not have a corresponding `llvm_points_to` statement in the
postconditions. Attempting to read from invalidated memory constitutes an
error, as can be seen in this portion of the error message when attempting to
verify `foo` against `foo_spec`:

:::{code-block} console
invalidate (state of memory allocated in precondition (at side.saw:3:12) not described in postcondition)
:::

To fix this particular issue, add an `llvm_points_to` statement to
`side_effect_spec`:

:::{code-block} sawscript
let side_effect_spec = do {
  a_ptr <- llvm_alloc (llvm_int 32);
  a_val <- llvm_fresh_var "a_val" (llvm_int 32);
  llvm_points_to a_ptr (llvm_term a_val);

  llvm_execute_func [a_ptr];

  // This is new
  llvm_points_to a_ptr (llvm_term {{ 0 : [32] }});
};
:::

After making this change, SAW will reject `foo_spec` for a different reason, as
it claims that `foo` returns its argument unchanged when it actually returns
`0`.

Note that invalidating memory itself does not constitute an error, so if the
`foo` function never read the value of `b` after calling `side_effect(&b)`,
then there would be no issue. It is only when a function attempts to _read_
from invalidated memory that an error is thrown. In general, it can be
difficult to predict when a function will or will not read from invalidated
memory, however. For this reason, it is recommended to always specify the
values of mutable allocations in the postconditions of your specs, as it can
avoid pitfalls like the one above.

The same pitfalls apply to compositional MIR verification, with a couple of key
differences. In MIR verification, mutable references are allocated using
`mir_alloc_mut`. Here is a Rust version of the pitfall program above:

:::{code-block} rust
pub fn side_effect(a: &mut u32) {
    *a = 0;
}

pub fn foo(x: u32) -> u32 {
    let mut b: u32 = x;
    side_effect(&mut b);
    b
}
:::

:::{code-block} sawscript
let side_effect_spec = do {
  a_ref <- mir_alloc_mut mir_u32;
  a_val <- mir_fresh_var "a_val" mir_u32;
  mir_points_to a_ref (mir_term a_val);

  mir_execute_func [a_ref];
};

let foo_spec = do {
  x <- mir_fresh_var "x" mir_u32;

  mir_execute_func [mir_term x];

  mir_return (mir_term {{ x }});
};
:::

Just like above, if you attempted to prove `foo` against `foo_spec` using
compositional verification:

:::{code-block} sawscript
side_effect_ov <- mir_verify m "test::side_effect" [] false side_effect_spec z3;
mir_verify m "test::foo" [side_effect_ov] false foo_spec z3;
:::

Then SAW would throw an error, as `side_effect_spec` underspecifies the value
of `a_ref` in its postconditions. `side_effect_spec` can similarly be repaired
by adding a `mir_points_to` statement involving `a_ref` in `side_effect_spec`'s
postconditions.

MIR verification differs slightly from LLVM verification in how it catches
underspecified mutable allocations when using compositional overrides. The LLVM
memory model achieves this by invalidating the underlying memory in
underspecified allocations. The MIR memory model, on the other hand, does not
have a direct counterpart to memory invalidation. As a result, any MIR overrides
must specify the values of all mutable allocations in their postconditions,
_even if the function that calls the override never uses the allocations_.

To illustrate this point more finely, suppose that the `foo` function had
instead been defined like this:

:::{code-block} rust
pub fn foo(x: u32) -> u32 {
    let mut b: u32 = x;
    side_effect(&mut b);
    42
}
:::

Here, it does not particularly matter what effects the `side_effect` function
has on its argument, as `foo` will now return `42` regardless. Still, if you
attempt to prove `foo` by using `side_effect` as a compositional override, then
it is strictly required that you specify the value of `side_effect`'s argument
in its postconditions, even though the answer that `foo` returns is unaffected
by this. This is in contrast with LLVM verification, where one could get away
without specifying `side_effect`'s argument in this example, as the invalidated
memory in `b` would never be read.

(compositional-verification-and-mutable-global-variables)=
#### Compositional Verification and Mutable Global Variables

Just like with local mutable allocations (see the previous section),
specifications used in compositional overrides must specify the values of
mutable global variables in their postconditions. To illustrate this using LLVM
verification, here is a variant of the C program from the previous example that
uses a mutable global variable `a`:

:::{code-block} c
uint32_t a = 42;

void side_effect(void) {
  a = 0;
}

uint32_t foo(void) {
  side_effect();
  return a;
}
:::

If we attempted to verify `foo` against this `foo_spec` specification using
compositional verification:

:::{code-block} sawscript
let side_effect_spec = do {
  llvm_alloc_global "a";
  llvm_points_to (llvm_global "a") (llvm_global_initializer "a");

  llvm_execute_func [];
};

let foo_spec = do {
  llvm_alloc_global "a";
  llvm_points_to (llvm_global "a") (llvm_global_initializer "a");

  llvm_execute_func [];

  llvm_return (llvm_global_initializer "a");
};

side_effect_ov <- llvm_verify m "side_effect" [] false side_effect_spec z3;
llvm_verify m "foo" [side_effect_ov] false foo_spec z3;
:::

Then SAW would reject it, as `side_effect_spec` does not specify what `a`'s
value should be in its postconditions. Just as with local mutable allocations,
SAW will invalidate the underlying memory in `a`, and subsequently reading from
`a` in the `foo` function will throw an error. The solution is to add an
`llvm_points_to` statement in the postconditions that declares that `a`'s value
is set to `0`.

The same concerns apply to MIR verification, where mutable global variables are
referred to as `static mut` items. (See the [MIR static
items](#mir-static-items) section for more information). Here is a Rust version
of the program above:

:::{code-block} rust
static mut A: u32 = 42;

pub fn side_effect() {
    unsafe {
        A = 0;
    }
}

pub fn foo() -> u32 {
    side_effect();
    unsafe { A }
}
:::

:::{code-block} sawscript
let side_effect_spec = do {
  mir_points_to (mir_static "test::A") (mir_static_initializer "test::A");

  mir_execute_func [];
};

let foo_spec = do {
  mir_points_to (mir_static "test::A") (mir_static_initializer "test::A");

  mir_execute_func [];

  mir_return (mir_static_initializer "test::A");
};

side_effect_ov <- mir_verify m "side_effect" [] false side_effect_spec z3;
mir_verify m "foo" [side_effect_ov] false foo_spec z3;
:::

Just as above, we can repair this by adding a `mir_points_to` statement in
`side_effect_spec`'s postconditions that specifies that `A` is set to `0`.

Recall from the previous section that MIR verification is stricter than LLVM
verification when it comes to specifying mutable allocations in the
postconditions of compositional overrides. This is especially true for mutable
static items. In MIR verification, any compositional overrides must specify the
values of all mutable static items in the entire program in their
postconditions, _even if the function that calls the override never uses the
static items_. For example, if the `foo` function were instead defined like
this:

:::{code-block} rust
pub fn foo() -> u32 {
    side_effect();
    42
}
:::

Then it is still required for `side_effect_spec` to specify what `A`'s value
will be in its postconditions, despite the fact that this has no effect on the
value that `foo` will return.


<!-- ------------------------------------------------------------ -->


## Using Ghost State

In some cases, information relevant to verification is not directly
present in the concrete state of the program being verified. This can
happen for at least two reasons:

- When providing specifications for external functions, for which source
  code is not present. The external code may read and write global state
  that is not directly accessible from the code being verified.

- When the abstract specification of the program naturally uses a
  different representation for some data than the concrete
  implementation in the code being verified does.

One solution to these problems is the use of _ghost_ state. This can be
thought of as additional global state that is visible only to the
verifier. Ghost state with a given name can be declared at the top level
with the following function:

- `declare_ghost_state : String -> TopLevel Ghost`

Ghost state variables do not initially have any particular type, and can
store data of any type. Given an existing ghost variable the following
functions can be used to specify its value:

- `llvm_ghost_value : Ghost -> Term -> LLVMSetup ()`
- `jvm_ghost_value  : Ghost -> Term -> JVMSetup  ()`
- `mir_ghost_value  : Ghost -> Term -> MIRSetup  ()`

These can be used in either prestate or poststate, to specify the
value of ghost state either before or after the execution of the function,
respectively.


<!-- ------------------------------------------------------------ -->


## Extracting Code

In many simple cases (such as the `max` function to return the largest of
two values), the relevant
inputs and outputs are immediately apparent. The function takes two integer
arguments, always uses both of them, and returns a single integer value,
making no other changes to the program state.

In cases like this, a direct translation to SAWCore is possible, given only an
identification of which code to execute.
Three functions exist to handle such simple code, one for each Crucible
backend:

- `llvm_extract : LLVMModule -> String -> TopLevel Term`
- `jvm_extract : JavaClass -> String -> TopLevel Term`
- `mir_extract : MIRModule -> String -> TopLevel Term`

The structure of these extraction functions is essentially identical.
The first argument describes where to look for code (in an LLVM module, Java
class, or MIR module, loaded as described above).
The second argument is the name of the method or function to extract.

When the extraction functions complete, they return a `Term`
corresponding to the value returned by the function or method as a
function of its arguments.

These functions currently work only for code that has specific argument and
result types:

- For `llvm_extract`, the extracted function must take some fixed
  number of integral parameters and return an integral result.

- For `jvm_extract`, the extracted function's argument and result types must
  be scalar types (i.e., not classes or arrays).

- For `mir_extract`, the extracted function's argument and result types must be
  a primitive integer type (e.g., `u8` or `i8`), a `bool`, a `char`, an array,
  or a tuple.

Although it is disallowed to extract functions that use pointers, classes, or
references in the extracted function's type signature, the implementation of
the extracted function is allowed to allocate memory during execution.
Also note the following requirements for interacting with global variables:

- For `llvm_extract`, the extracted function is allowed to read from immutable
  global variables during execution, but it is not allowed to read or write
  from mutable global variables during execution.

- For `jvm_extract`, the extracted function is allowed to read from or write
  to any class field or static field (regardless of mutability) during
  execution.
  The class and static fields will be given their initial values during
  extraction (unless they are overwritten during execution).

- For `mir_extract`, the extracted function is allowed to read from immutable
  static items during execution, and it is allowed to write to mutable static
  items during execution.
  The extracted function is not allowed to read from a mutable static item
  during execution unless the function has written another value to the static
  item earlier during execution.


<!-- ------------------------------------------------------------ -->


<!--
   XXX I'm commenting this whole section out. It should probably get
   deleted, but not quite yet.

   Constructing SAWCore lambdas this way is both super-awkward, ugly,
   and not really safe. Meanwhile, `fresh_symbolic` hallucinates
   SAWCore variables into existence without declaring them, and any
   use that _doesn't_ involve creating lambdas is abusive. The whole
   lot should be removed in favor of SAWCore quasiquotation.
-->

<!--

## Creating Symbolic Variables

The direct extraction process discussed previously introduces
symbolic variables and then abstracts over them, yielding a SAWScript
`Term` that reflects the semantics of the original Java, LLVM, or MIR code.
For simple functions, this is often the most convenient interface. For
more complex code, however, it can be necessary (or more natural) to
specifically introduce fresh variables and indicate what portions of the
program state they correspond to.

- `fresh_symbolic : String -> Type -> TopLevel Term` is responsible for
creating new variables in this context. The first argument is a name
used for pretty-printing of terms and counter-examples. In many cases it
makes sense for this to be the same as the name used within SAWScript,
as in the following:

:::{code-block} sawscript
x <- fresh_symbolic "x" ty;
:::

However, using the same name is not required.

The second argument to `fresh_symbolic` is the type of the fresh
variable. Ultimately, this will be a SAWCore type; however, it is usually
convenient to specify it using Cryptol syntax with the type quoting
brackets `{|` and `|}`. For example, creating a 32-bit integer, as
might be used to represent a Java `int` or an LLVM `i32`, can be done as
follows:

:::{code-block} sawscript
x <- fresh_symbolic "x" {| [32] |};
:::

Although symbolic execution works best on symbolic variables, which are
"unbound" or "free", most of the proof infrastructure within SAW uses
variables that are _bound_ by an enclosing lambda expression. Given a
`Term` with free symbolic variables, we can construct a lambda term that
binds them in several ways.

- `abstract_symbolic : Term -> Term` finds all symbolic variables in the
`Term` and constructs a lambda expression binding each one, in some
order. The result is a function of some number of arguments, one for
each symbolic variable. It is the simplest but least flexible way to
bind symbolic variables.

:::{code-block} console
sawscript> x <- fresh_symbolic "x" {| [8] |}
sawscript> let t = {{ x + x }}
sawscript> print_term t
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8))
      x
      x
sawscript> let f = abstract_symbolic t
sawscript> print_term f
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in \(x : x@1) ->
      Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8)) x x
:::

If there are multiple symbolic variables in the `Term` passed to
`abstract_symbolic`, the ordering of parameters can be hard to predict.
In some cases (such as when a proof is the immediate next step, and it's
expected to succeed) the order isn't important. In others, it's nice to
have more control over the order.

- `lambda : Term -> Term -> Term` is the building block for controlled
binding. It takes two terms: the one to transform, and the portion of
the term to abstract over. Generally, the first `Term` is one obtained
from `fresh_symbolic` and the second is a `Term` that would be passed to
`abstract_symbolic`.

:::{code-block} console
sawscript> let f = lambda x t
sawscript> print_term f
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in \(x : x@1) ->
      Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8)) x x
:::

- `lambdas : [Term] -> Term -> Term` allows you to list the order in which
symbolic variables should be bound. Consider, for example, a `Term`
which adds two symbolic variables:

:::{code-block} console
sawscript> x1 <- fresh_symbolic "x1" {| [8] |}
sawscript> x2 <- fresh_symbolic "x2" {| [8] |}
sawscript> let t = {{ x1 + x2 }}
sawscript> print_term t
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8))
      x1
      x2
:::

We can turn `t` into a function that takes `x1` followed by `x2`:

:::{code-block} console
sawscript> let f1 = lambdas [x1, x2] t
sawscript> print_term f1
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in \(x1 : x@1) ->
      \(x2 : x@1) ->
        Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8)) x1
          x2
:::

Or we can turn `t` into a function that takes `x2` followed by `x1`:

:::{code-block} console
sawscript> let f1 = lambdas [x2, x1] t
sawscript> print_term f1
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in \(x2 : x@1) ->
      \(x1 : x@1) ->
        Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8)) x1
          x2
:::

-->


<!-- ------------------------------------------------------------ -->


## A Heap-Based Example

To tie all of the command descriptions from the previous sections
together, consider the case of verifying the correctness of a C program
that computes the dot product of two vectors, where the length and value
of each vector are encapsulated together in a `struct`.

The dot product can be concisely specified in Cryptol as follows:

:::{code-block} cryptol
dotprod : {n, a} (fin n, fin a) => [n][a] -> [n][a] -> [a]
dotprod xs ys = sum (zip (*) xs ys)
:::

To implement this in C, let's first consider the type of vectors:

:::{code-block} c
typedef struct {
    uint32_t *elts;
    uint32_t size;
} vec_t;
:::

This struct contains a pointer to an array of 32-bit elements, and a
32-bit value indicating how many elements that array has.

We can compute the dot product of two of these vectors with the
following C code (which uses the size of the shorter vector if they
differ in size).

:::{code-block} c
uint32_t dotprod_struct(vec_t *x, vec_t *y) {
    uint32_t size = MIN(x->size, y->size);
    uint32_t res = 0;
    for(size_t i = 0; i < size; i++) {
        res += x->elts[i] * y->elts[i];
    }
    return res;
}
:::

The entirety of this implementation can be found in the
`examples/llvm/dotprod_struct.c` file in the `saw-script` repository.

To verify this program in SAW, it will be convenient to define a couple
of utility functions (which are generally useful for many
heap-manipulating programs). First, combining allocation and
initialization to a specific value can make many scripts more concise:

:::{code-block} sawscript
let alloc_init ty v = do {
    p <- llvm_alloc ty;
    llvm_points_to p v;
    return p;
};
:::

This creates a pointer `p` pointing to enough space to store type `ty`,
and then indicates that the pointer points to value `v` (which should be
of that same type).

A common case for allocation and initialization together is when the
initial value should be entirely symbolic.

:::{code-block} sawscript
let ptr_to_fresh n ty = do {
    x <- llvm_fresh_var n ty;
    p <- alloc_init ty (llvm_term x);
    return (x, p);
};
:::

This function returns the pointer just allocated along with the fresh
symbolic value it points to.

Given these two utility functions, the `dotprod_struct` function can be
specified as follows:

:::{code-block} sawscript
let dotprod_spec n = do {
    let nt = llvm_term {{ `n : [32] }};
    (xs, xsp) <- ptr_to_fresh "xs" (llvm_array n (llvm_int 32));
    (ys, ysp) <- ptr_to_fresh "ys" (llvm_array n (llvm_int 32));
    let xval = llvm_struct_value [ xsp, nt ];
    let yval = llvm_struct_value [ ysp, nt ];
    xp <- alloc_init (llvm_alias "struct.vec_t") xval;
    yp <- alloc_init (llvm_alias "struct.vec_t") yval;
    llvm_execute_func [xp, yp];
    llvm_return (llvm_term {{ dotprod xs ys }});
};
:::

Any instantiation of this specification is for a specific vector length
`n`, and assumes that both input vectors have that length. That length
`n` automatically becomes a type variable in the subsequent Cryptol
expressions, and the backtick operator is used to reify that type as a
bit vector of length 32.

The entire script can be found in the `dotprod_struct-crucible.saw` file
alongside `dotprod_struct.c`.

Running this script results in the following:

:::{code-block} console
Loading file "dotprod_struct.saw"
Proof succeeded! dotprod_struct
Registering override for `dotprod_struct`
  variant `dotprod_struct`
Symbolic simulation completed with side conditions.
Proof succeeded! dotprod_wrap
:::


<!-- ------------------------------------------------------------ -->


## An Extended Example

To tie together many of the concepts in this manual, we now present a
non-trivial verification task in its entirety. All of the code for this example
can be found in the `examples/salsa20` directory of
[the SAWScript repository](https://github.com/GaloisInc/saw-script).

### Salsa20 Overview

Salsa20 is a stream cipher developed in 2005 by Daniel J. Bernstein, built on a
pseudorandom function utilizing add-rotate-XOR (ARX) operations on 32-bit
words[^4]. Bernstein himself has provided several public domain
implementations of the cipher, optimized for common machine architectures.
For the mathematically inclined, his specification for the cipher can be
found [here](http://cr.yp.to/snuffle/spec.pdf).

The repository referenced above contains three implementations of the Salsa20
cipher: A reference Cryptol implementation (which we take as correct in this
example), and two C implementations, one of which is from Bernstein himself.
For this example, we focus on the second of these C
implementations, which more closely matches the Cryptol implementation. Full
verification of Bernstein's implementation is available in
`examples/salsa20/djb`, for the interested. The code for this verification task
can be found in the files named according to the pattern
`examples/salsa20/(s|S)alsa20.*`.

### Specifications

We now take on the actual verification task. This will be done in two stages:
We first define some useful utility functions for constructing common patterns
in the specifications for this type of program (i.e. one where the arguments to
functions are modified in-place.) We then demonstrate how one might construct a
specification for each of the functions in the Salsa20 implementation described
above.

#### Utility Functions

We first define the function
`alloc_init : LLVMType -> Term -> LLVMSetup LLVMValue`.

`alloc_init ty v` returns a `LLVMValue` consisting of a pointer to memory
allocated and initialized to a value `v` of type `ty`. `alloc_init_readonly`
does the same, except the memory allocated cannot be written to.

:::{code-block} sawscript
import "Salsa20.cry";

let alloc_init ty v = do {
    p <- llvm_alloc ty;
    llvm_points_to p (llvm_term v);
    return p;
};

let alloc_init_readonly ty v = do {
    p <- llvm_alloc_readonly ty;
    llvm_points_to p (llvm_term v);
    return p;
};
:::

We now define
`ptr_to_fresh : String -> LLVMType -> LLVMSetup (Term, LLVMValue)`.

`ptr_to_fresh n ty` returns a pair `(x, p)` consisting of a fresh symbolic
variable `x` of type `ty` and a pointer `p` to it. `n` specifies the
name that SAW should use when printing `x`. `ptr_to_fresh_readonly` does the
same, but returns a pointer to space that cannot be written to.

:::{code-block} sawscript
let ptr_to_fresh n ty = do {
    x <- llvm_fresh_var n ty;
    p <- alloc_init ty x;
    return (x, p);
};

let ptr_to_fresh_readonly n ty = do {
    x <- llvm_fresh_var n ty;
    p <- alloc_init_readonly ty x;
    return (x, p);
};
:::

Finally, we define
`oneptr_update_func : String -> LLVMType -> Term -> LLVMSetup ()`.

`oneptr_update_func n ty f` specifies the behavior of a function that takes
a single pointer (with a printable name given by `n`) to memory containing a
value of type `ty` and mutates the contents of that memory. The specification
asserts that the contents of this memory after execution are equal to the value
given by the application of `f` to the value in that memory before execution.

:::{code-block} sawscript
let oneptr_update_func n ty f = do {
    (x, p) <- ptr_to_fresh n ty;
    llvm_execute_func [p];
    llvm_points_to p (llvm_term {{ f x }});
};
:::

#### The `quarterround` operation

The C function we wish to verify has type
`void s20_quarterround(uint32_t *y0, uint32_t *y1, uint32_t *y2, uint32_t *y3)`.

The function's specification generates four symbolic variables and pointers to
them in the precondition/setup stage. The pointers are passed to the function
during symbolic execution via `llvm_execute_func`. Finally, in the
postcondition/return stage, the expected values are computed using the trusted
Cryptol implementation and it is asserted that the pointers do in fact point to
these expected values.

:::{code-block} sawscript
let quarterround_setup : LLVMSetup () = do {
    (y0, p0) <- ptr_to_fresh "y0" (llvm_int 32);
    (y1, p1) <- ptr_to_fresh "y1" (llvm_int 32);
    (y2, p2) <- ptr_to_fresh "y2" (llvm_int 32);
    (y3, p3) <- ptr_to_fresh "y3" (llvm_int 32);

    llvm_execute_func [p0, p1, p2, p3];

    let zs = {{ quarterround [y0,y1,y2,y3] }}; // from Salsa20.cry
    llvm_points_to p0 (llvm_term {{ zs@0 }});
    llvm_points_to p1 (llvm_term {{ zs@1 }});
    llvm_points_to p2 (llvm_term {{ zs@2 }});
    llvm_points_to p3 (llvm_term {{ zs@3 }});
};
:::

#### Simple Updating Functions

The following functions can all have their specifications given by the utility
function `oneptr_update_func` implemented above, so there isn't much to say
about them.

:::{code-block} sawscript
let rowround_setup =
    oneptr_update_func "y" (llvm_array 16 (llvm_int 32)) {{ rowround }};

let columnround_setup =
    oneptr_update_func "x" (llvm_array 16 (llvm_int 32)) {{ columnround }};

let doubleround_setup =
    oneptr_update_func "x" (llvm_array 16 (llvm_int 32)) {{ doubleround }};

let salsa20_setup =
    oneptr_update_func "seq" (llvm_array 64 (llvm_int 8)) {{ Salsa20 }};
:::

#### 32-Bit Key Expansion

The next function of substantial behavior that we wish to verify has the
following prototype:

:::{code-block} c
void s20_expand32( uint8_t *k
                 , uint8_t n[static 16]
                 , uint8_t keystream[static 64]
                 )
:::

This function's specification follows a similar pattern to that of
`s20_quarterround`, though for extra assurance we can make sure that the
function does not write to the memory pointed to by `k` or `n` using the
utility `ptr_to_fresh_readonly`, as this function should only modify
`keystream`. Besides this, we see the call to the trusted Cryptol
implementation specialized to `a=2`, which does 32-bit key expansion (since the
Cryptol implementation can also specialize to `a=1` for 16-bit keys). This
specification can easily be changed to work with 16-bit keys.

:::{code-block} sawscript
let salsa20_expansion_32 = do {
    (k, pk) <- ptr_to_fresh_readonly "k" (llvm_array 32 (llvm_int 8));
    (n, pn) <- ptr_to_fresh_readonly "n" (llvm_array 16 (llvm_int 8));

    pks <- llvm_alloc (llvm_array 64 (llvm_int 8));

    llvm_execute_func [pk, pn, pks];

    let rks = {{ Salsa20_expansion`{a=2}(k, n) }};
    llvm_points_to pks (llvm_term rks);
};
:::

#### 32-bit Key Encryption

Finally, we write a specification for the encryption function itself, which has
type

:::{code-block} c
enum s20_status_t s20_crypt32( uint8_t *key
                             , uint8_t nonce[static 8]
                             , uint32_t si
                             , uint8_t *buf
                             , uint32_t buflen
                             )
:::

As before, we can ensure this function does not modify the memory pointed to by
`key` or `nonce`. We take `si`, the stream index, to be 0. The specification is
parameterized on a number `n`, which corresponds to `buflen`. Finally, to deal
with the fact that this function returns a status code, we simply specify that
we expect a success (status code 0) as the return value in the postcondition
stage of the specification.

:::{code-block} sawscript
let s20_encrypt32 n = do {
    (key, pkey) <- ptr_to_fresh_readonly "key" (llvm_array 32 (llvm_int 8));
    (v, pv) <- ptr_to_fresh_readonly "nonce" (llvm_array 8 (llvm_int 8));
    (m, pm) <- ptr_to_fresh "buf" (llvm_array n (llvm_int 8));

    llvm_execute_func [ pkey
                      , pv
                      , llvm_term {{ 0 : [32] }}
                      , pm
                      , llvm_term {{ `n : [32] }}
                      ];

    llvm_points_to pm (llvm_term {{ Salsa20_encrypt (key, v, m) }});
    llvm_return (llvm_term {{ 0 : [32] }});
};
:::

### Verifying Everything

Finally, we can verify all of the functions. Notice the use of compositional
verification and that path satisfiability checking is enabled for those
functions with loops not bounded by explicit constants. Notice that we prove
the top-level function for several sizes; this is due to the limitation that
SAW can only operate on finite programs (while Salsa20 can operate on any input
size.)

:::{code-block} sawscript
let main : TopLevel () = do {
    m      <- llvm_load_module "salsa20.bc";
    qr     <- llvm_verify m "s20_quarterround" []      false quarterround_setup   abc;
    rr     <- llvm_verify m "s20_rowround"     [qr]    false rowround_setup       abc;
    cr     <- llvm_verify m "s20_columnround"  [qr]    false columnround_setup    abc;
    dr     <- llvm_verify m "s20_doubleround"  [cr,rr] false doubleround_setup    abc;
    s20    <- llvm_verify m "s20_hash"         [dr]    false salsa20_setup        abc;
    s20e32 <- llvm_verify m "s20_expand32"     [s20]   true  salsa20_expansion_32 abc;
    s20encrypt_63 <- llvm_verify m "s20_crypt32" [s20e32] true (s20_encrypt32 63) abc;
    s20encrypt_64 <- llvm_verify m "s20_crypt32" [s20e32] true (s20_encrypt32 64) abc;
    s20encrypt_65 <- llvm_verify m "s20_crypt32" [s20e32] true (s20_encrypt32 65) abc;

    print "Done!";
};
:::

[^4]: <https://en.wikipedia.org/wiki/Salsa20>


<!-- ------------------------------------------------------------ -->


## Verifying Cryptol FFI functions

SAW has special support for verifying the correctness of Cryptol's
[`foreign`
functions](https://galoisinc.github.io/cryptol/master/FFI.html),
implemented in a language such as C which compiles to LLVM, provided
that there exists a [reference Cryptol
implementation](https://galoisinc.github.io/cryptol/master/FFI.html#cryptol-implementation-of-foreign-functions)
of the function as well. Since the way in which `foreign` functions are
called is precisely specified by the Cryptol FFI, SAW is able to
generate a `LLVMSetup ()` spec directly from the type of a Cryptol
`foreign` function. This is done with the `llvm_ffi_setup` command,
which is experimental and requires `enable_experimental;` to be run
beforehand.

- `llvm_ffi_setup : Term -> LLVMSetup ()`

For instance, for the simple imported Cryptol foreign function `foreign
add : [32] -> [32] -> [32]` we can obtain a `LLVMSetup` spec simply by
writing

:::{code-block} sawscript
let add_setup = llvm_ffi_setup {{ add }};
:::

which behind the scenes expands to something like

:::{code-block} sawscript
let add_setup = do {
  in0 <- llvm_fresh_var "in0" (llvm_int 32);
  in1 <- llvm_fresh_var "in1" (llvm_int 32);
  llvm_execute_func [llvm_term in0, llvm_term in1];
  llvm_return (llvm_term {{ add in0 in1 }});
};
:::

### Polymorphism

In general, Cryptol `foreign` functions can be polymorphic, with type
parameters of kind `#` (number types), representing e.g. the sizes of
input sequences.
However, any individual `LLVMSetup ()` spec only specifies the behavior
of the LLVM function on inputs of concrete sizes. We handle this by
allowing the argument term of `llvm_ffi_setup` to contain any necessary
type arguments in addition to the Cryptol function name, so that the
resulting term is monomorphic. The user can then define a parameterized
specification simply as a SAWScript function in the usual way. For
example, for a function `foreign f : {n, m} (fin n, fin m) => [n][32] ->
[m][32]`, we can obtain a parameterized `LLVMSetup` spec by

:::{code-block} sawscript
let f_setup (n : Int) (m : Int) = llvm_ffi_setup {{ f`{n, m} }};
:::

Note that the `Term` parameter that `llvm_ffi_setup` takes is restricted
syntactically to the format described above (``{{ fun`{tyArg0, tyArg1,
..., tyArgN} }}``), and cannot be any arbitrary term.

### Supported types

`llvm_ffi_setup` supports all Cryptol types that are supported by the
Cryptol FFI, with the exception of `Integer`, `Rational`, `Z`, and
`Float`. `Integer`, `Rational`, and `Z` are not supported since they are
translated to `gmp` arbitrary-precision types which are hard for SAW to
handle without additional overrides. There is no fundamental obstacle to
supporting `Float`, and in fact `llvm_ffi_setup` itself does work with
Cryptol floating point types, but the underlying functions such as
`llvm_fresh_var` do not, so until that is implemented `llvm_ffi_setup`
can generate a spec involving floating point types but it cannot
actually be run.

Note also that for the time being only the `c` calling convention is
supported.
Support for the recently-added `abstract` calling convention has not
been written yet.
See [issue #2546](https://github.com/GaloisInc/saw-script/issues/2546).

### Performing the verification

The resulting `LLVMSetup ()` spec can be used with the existing
`llvm_verify` function to perform the actual verification. And the
`LLVMSpec` output from that can be used as an override as usual for
further compositional verification.

:::{code-block} sawscript
f_ov <- llvm_verify mod "f" [] true (f_setup 3 5) z3;
:::

As with the Cryptol FFI itself, SAW does not manage the compilation of
the C source implementations of `foreign` functions to LLVM bitcode. For
the verification to be meaningful, is expected that the LLVM module
passed to `llvm_verify` matches the compiled dynamic library actually
used with the Cryptol interpreter. Alternatively, on x86_64 Linux, SAW
can perform verification directly on the `.so` ELF file with the
experimental `llvm_verify_x86` command.


<!-- ------------------------------------------------------------ -->


## Multi-Step Proofs and Loop Invariants with Cuts

The LLVM backend (and so far, only the LLVM backend) has the ability
to divide a function under verification into two (or more) parts and
apply assertions at the middle point as well as the beginning and end.
This is called a "cut", after the similar operation in proof
derivations, and we call the point of division a "cutpoint".

This feature is highly experimental (not to mention complicated and
confusing) and should be approached with caution.

At the code level, the cutpoint is a call to an empty placeholder
function with a magic name.
This does require modifying the code, although not in a way that has
any material effect.

When verifying, SAW recognizes the magic name when loading the LLVM
module and transforms the code by moving the rest of the code in the
real function to the placeholder function and replacing it with a
call to the placeholder.

Then one may write SAW specifications for the original function name
(representing the whole original function) and for the placeholder
function (representing only the second part of it).

The magic names SAW recognizes and applies this feature to are any
function names beginning with `__cutpoint__`.

A simple example of a two-stage function, adapted from SAW's test
suite (see `intTests/test_cutpoint`):

:::{code-block} c
#include <stdlib.h>

extern size_t __cutpoint__add2(size_t *);

size_t add2(size_t x) {
  ++x;
  __cutpoint__add2(&x);
  ++x;
  return x;
}
:::

This function adds two to its argument in separate steps, and we'll
verify each half separately.

Note that the function `__cutpoint_add2` does not actually exist in
this example, and does not need to for verification.
It only exists to mark the cut.
(If you wanted to run this code, you'd provide an empty implementation
that does nothing.)

The corresponding SAW specifications are, first for `add2`:

:::{code-block} sawscript
let add2_spec = do {
  x <- llvm_fresh_var "x" (llvm_int 64);
  llvm_execute_func [llvm_term x];
  llvm_return (llvm_term {{ x + 2 }});
};
:::

And for `__cutpoint__add2`:

:::{code-block} sawscript
let cutpoint_add2_spec = do {
  p <- llvm_alloc (llvm_int 64);
  x <- llvm_fresh_var "x" (llvm_int 64);
  llvm_points_to p (llvm_term x);
  llvm_execute_func [p];
  llvm_return (llvm_term {{ x + 1 }});
};
:::

There are several things to note here.
First, the spec for `add2` spans the whole function: the return value
it specifies is the overall return value, not the value of `x` at the
cutpoint.
There is no direct way to address the value of `x` at the cutpoint
in the spec for the original function.
The spec for the cutpoint function receives that value of `x`, and can
write assertions about it, but there is in turn no easy way to get at
the original value of `x` as of entry to `add2`.
(The only way to do so is to change the code around to preserve it in
another variable, which is almost always undesirable.)
The verification will check that that the value of `x` as of the
cutpoint satisfies the precondition given in the cutpoint function
spec.
However, for complex code these limitations may make writing that
precondition difficult or impossible.
(We might extend or alter the behavior in the future to make it
possible.
As noted above the feature is experimental; it has some sharp edges,
of which this is one.)

Second, the spec for `cutpoint_add2` always covers the entire
remainder of the function.
If you use two cutpoints to divide a function into three parts, the
first spec spans the whole function, the second spans the second and
third part, and the third spans only the third part.
There is (currently) no way to flip this around so the first spec
spans just the first part of the function and the last spans the
whole function.

Third, the value of x is passed to the cutpoint through a pointer.
This is necessary to make the propagation of the values through the
transformed code work properly.
It is also necessary to pass the values of all live variables, via
pointers, to the cutpoint function, in the order they appear in the
LLVM stack frame.
Determining which variables these are and what order they appear in
may require disassembling the LLVM bitcode (with `llvm-dis` or
SAW's `:llvmdis` REPL command) and inspecting it.
As of this writing, if any of this is not correct, SAW crashes deep
inside the logic that performs the code transformation, and, alas,
with a fairly mysterious message about being unable to find register
values.

Now, to verify this function you do the following, assuming that
`m` is the LLVM module:

:::{code-block} sawscript
cp <- llvm_verify m "__cutpoint__add2#add2" [] true cutpoint_add2_spec z3;
llvm_verify m "add2" [cp] true add2_spec z3;
:::

That is: first you verify the cutpoint function against its spec, then
you use it as an override when verifying the original function.

Note the extra bit in the name in the first `llvm_verify` call: you
must provide the name of the parent function after a `#`.
SAW needs this to find the transformed code.

### Applying Cuts Under Conditionals

If you place a cutpoint in a block that is conditionally executed
(e.g. inside an if whose control is not constant) the cutpoint function
still continues for the entire remainder of the function.
Thus, the spec for the cutpoint function must include the behavior of
all the code that occurs after it, not just the contents of the conditional
block.
However, it does not need to reason about the other branch of the
conditional at all.

Similarly, if you place cutpoints in both sides of a conditional, both
cutpoint specs must cover the entire remainder of the function.
However, in some situations this can allow being more specific about
what happens than is easily done without the cutpoints.

This can sometimes be helpful for handling functions with
diamond-shaped control flow.

You cannot, unfortunately, splice the execution back together after
the conditionals have ended.

Note that while the spec for the whole function must still give some
overall return value, that characterizes what happens after both sides
of the conditional, it need not necessarily be fully specific about
it.

### Using Cut with Loops

While dividing a large or complicated sequential function into
multiple parts can be useful in its own right, the real purpose of the
cut feature is to allow reasoning about loops by providing loop
invariants.

When you place a cutpoint in the condition of a loop, the cutpoint
function becomes the rest of the original function... which is to say,
it executes the loop body and then comes back to the loop condition.
In particular, the loop is converted into recursion and the recursive
call becomes another call to the cutpoint function.
This makes the precondition of the cutpoint function a loop invariant.

It also means you can escape SAW's restriction about loops being
concretely bounded.
The trick is to first assume the spec for the cutpoint function, then
use that as an override when proving it.
The proof will check that the loop body correctly assumes and then
restores the loop invariant, and the override using the assumed
version will let SAW conclude that the loop invariant remains true
after the recursive call without having to execute through it again.

However, beware: this technique only provides partial correctness.
It does not allow reasoning about the termination of the loop.
It allows you to prove that _if_ the loop terminates, the original
function returns according to the spec.
If the loop doesn't terminate, it doesn't terminate.

Here is an example, also adapted from the test suite:

:::{code-block} c
#include <stdlib.h>

extern size_t __cutpoint__inv(size_t*, size_t*, size_t*) __attribute__((noduplicate));

size_t count_n(size_t n) {
  size_t c = 0;
  for (size_t i = 0; __cutpoint__inv(&n, &c, &i), i < n; ++i) {
    ++c;
  }
  return c;
}
:::

This rather naively counts up to `n`.
SAW can't handle this function by default, or at least not in general:
you can prove it works for any given value of `n`, but proving a
general theorem about it for all `n` requires it to try the loop all
`n` times.
(Because `n` is a bitvector, that's at least not infinitely many
times; however, because it's a 64-bit bitvector, it is too many to
check in any effective amount of time.)

Instead we can write this spec for the cutpoint:

:::{code-block} sawscript
let ptr_to_fresh n ty = do {
  p <- llvm_alloc ty;
  x <- llvm_fresh_var n ty;
  llvm_points_to p (llvm_term x);
  return (p, x);
};

let inv_spec = do {
  (pn, n) <- ptr_to_fresh "n" (llvm_int 64);
  (pc, c) <- ptr_to_fresh "c" (llvm_int 64);
  (pi, i) <- ptr_to_fresh "i" (llvm_int 64);
  llvm_precond {{ 0 <= i /\ i <= n }};
  llvm_execute_func [pn, pc, pi];
  llvm_return (llvm_term {{ c + (n - i) }});
};
:::

This is about what one would expect: it takes all three of the live
variables as pointer arguments, and the loop invariant is the loop
condition extended to the case where the loop terminates.

The return value seems slightly unexpected; surely the return value
should be just `n`?
If you try that, it doesn't work.
But that's because the loop invariant isn't strong enough; it doesn't
say anything about the relationship of `c` and `i`.

What's here is true even if they are out of sync: when the loop
terminates (if it terminates), `i` is equal to `n` and we return
`c`, whatever it is, which is what the C code does.

One can also write this spec:

:::{code-block} sawscript
let inv_spec = do {
  (pn, n) <- ptr_to_fresh "n" (llvm_int 64);
  (pc, c) <- ptr_to_fresh "c" (llvm_int 64);
  (pi, i) <- ptr_to_fresh "i" (llvm_int 64);
  llvm_precond {{ 0 <= i /\ i <= n /\ c == i }};
  llvm_execute_func [pn, pc, pi];
  llvm_return (llvm_term {{ n }});
};
:::

and this will also verify.

However, in either case this spec for the original function will
still verify successfully:

:::{code-block} sawscript
let count_n_spec = do {
  n <- llvm_fresh_var "n" (llvm_int 64);
  llvm_execute_func [llvm_term n];
  llvm_return (llvm_term n);
};
:::

Verifying this function only reaches the loop when `c` and `n` are
equal, and that's sufficient for SAW to show that, because `i` is
equal to `n` when the loop terminates (if it terminates), `c` is also
equal to `n`.

Choosing the correct loop invariant is a sometimes subtle art.
(It is not in any way SAW-specific and much has been written about it
elsewhere.)

Note however that as with the sequential usage, the whole rest of the
function after the loop belongs to the cutpoint function; if there is
code after the loop, the cutpoint spec needs to account for it.

This is how you actually run the verification:

:::{code-block} sawscript
inv <- llvm_unsafe_assume_spec m "__cutpoint__inv#count_n" inv_spec;
llvm_verify m "__cutpoint__inv#count_n" [inv] false inv_spec abc;
llvm_verify m "count_n" [inv] false count_n_spec abc;
:::

As described above, first you assume the spec for the cutpoint
function, then you verify it using the assumed version as an override
for the recursive call.
(This is a proof by induction: the code leading up to the loop is the
base case that establishes the inductive hypothesis, which is the loop
invariant; then the loop body is the inductive case.
Then for any finite number of iterations the loop invariant holds, and
so it holds when the loop terminates... if it terminates.)

Notice that the cutpoint function is labeled `noduplicate`; this
prevents LLVM from doing optimizations that might break SAW's ability
to do the cut transform.
