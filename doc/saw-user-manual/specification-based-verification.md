# Specification-Based Verification

The built-in functions described so far work by extracting models of
code that can then be used for a variety of purposes, including proofs
about the properties of the code.

When the goal is to prove equivalence between some LLVM, Java, or MIR code and
a specification, however, a more declarative approach is sometimes
convenient. The following sections describe an approach that combines
model extraction and verification with respect to a specification. A
verified specification can then be used as input to future
verifications, allowing the proof process to be decomposed.

## Running a Verification

Verification of LLVM is controlled by the `llvm_verify` command.

:::{code-block} sawscript
llvm_verify :
  LLVMModule ->
  String ->
  [CrucibleMethodSpec] ->
  Bool ->
  LLVMSetup () ->
  ProofScript SatResult ->
  TopLevel CrucibleMethodSpec
:::

The first two arguments specify the module and function name to verify,
as with `llvm_verify`. The third argument specifies the list of
already-verified specifications to use for compositional verification
(described later; use `[]` for now). The fourth argument specifies
whether to do path satisfiability checking, and the fifth gives the
specification of the function to be verified. Finally, the last argument
gives the proof script to use for verification. The result is a proved
specification that can be used to simplify verification of functions
that call this one.

Similar commands are available for JVM programs:

:::{code-block} sawscript
jvm_verify :
  JavaClass ->
  String ->
  [JVMMethodSpec] ->
  Bool ->
  JVMSetup () ->
  ProofScript SatResult ->
  TopLevel JVMMethodSpec
:::

And for MIR programs:

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

### Running a MIR-based verification

(Note: API functions involving MIR verification require `enable_experimental`
in order to be used. As such, some parts of this API may change before being
finalized.)

The `String` supplied as an argument to `mir_verify` is expected to be a
function _identifier_. An identifier is expected adhere to one of the following
conventions:

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

  Where `core` is the crate name and `ptr::read` is the function path, which
  has two segments `ptr` and `read`. There are also some special forms of
  segments that appear for functions defined in certain language constructs.
  For instance, if a function is defined in an `impl` block, then it will have
  `{impl}` as one of its segments, e.g.,

  :::{code-block} text
  core::ptr::const_ptr::{impl}::offset
  :::

  If you are in doubt about what the full identifier for a given function is,
  consult the MIR JSON file for your program.

  The Rust compiler generates a separate instance for each use of a polymorphic
  function at a different type.   These instances have a compiler generated
  name, so the easiest way to refer to them is by using the command
  `mir_find_name : MIRModule -> String -> [MIRType] -> String`.
  Given a Rust module, the name of a polymorphic function, and a list of types,
  `mir_find_name` will return the name of the corresponding instantion.
  It throws an exception if the polymorphic function or the given
  instantiation are not found.

-----

Now we describe how to construct a value of type `LLVMSetup ()`, `JVMSetup ()`,
or `MIRSetup ()`.

## Structure of a Specification

A specifications for Crucible consists of three logical components:

- A specification of the initial state before execution of the function.

- A description of how to call the function within that state.

- A specification of the expected final value of the program state.

These three portions of the specification are written in sequence within a `do`
block of type `{LLVM,JVM,MIR}Setup`. The command `{llvm,jvm,mir}_execute_func`
separates the specification of the initial state from the specification of the
final state, and specifies the arguments to the function in terms of the
initial state. Most of the commands available for state description will work
either before or after `{llvm,jvm,mir}_execute_func`, though with slightly
different meaning, as described below.

## Creating Fresh Variables

In any case where you want to prove a property of a function for an entire
class of inputs (perhaps all inputs) rather than concrete values, the initial
values of at least some elements of the program state must contain fresh
variables. These are created in a specification with the
`{llvm,jvm,mir}_fresh_var` commands rather than `fresh_symbolic`.

- `llvm_fresh_var : String -> LLVMType -> LLVMSetup Term`

- `jvm_fresh_var : String -> JavaType -> JVMSetup Term`

- `mir_fresh_var : String -> MIRType -> MIRSetup Term`

The first parameter to both functions is a name, used only for
presentation. It's possible (though not recommended) to create multiple
variables with the same name, but SAW will distinguish between them
internally. The second parameter is the LLVM, Java, or MIR type of the
variable. The resulting `Term` can be used in various subsequent
commands.

Note that the second parameter to `{llvm,jvm,mir}_fresh_var` must be a type
that has a counterpart in Cryptol. (For more information on this, refer to the
"Cryptol type correspondence" section.) If the type does not have a Cryptol
counterpart, the function will raise an error. If you do need to create a fresh
value of a type that cannot be represented in Cryptol, consider using a
function such as `llvm_fresh_expanded_val` (for LLVM verification) or
`mir_fresh_expanded_value` (for MIR verification).

LLVM types are built with this set of functions:

- `llvm_int : Int -> LLVMType`
- `llvm_alias : String -> LLVMType`
- `llvm_array : Int -> LLVMType -> LLVMType`
- `llvm_float : LLVMType`
- `llvm_double : LLVMType`
- `llvm_packed_struct : [LLVMType] -> LLVMType`
- `llvm_struct_type : [LLVMType] -> LLVMType`

Java types are built up using the following functions:

- `java_bool : JavaType`
- `java_byte : JavaType`
- `java_char : JavaType`
- `java_short : JavaType`
- `java_int : JavaType`
- `java_long : JavaType`
- `java_float : JavaType`
- `java_double : JavaType`
- `java_class : String -> JavaType`
- `java_array : Int -> JavaType -> JavaType`

MIR types are built up using the following functions:

- `mir_adt : MIRAdt -> MIRType`
- `mir_array : Int -> MIRType -> MIRType`
- `mir_bool : MIRType`
- `mir_char : MIRType`
- `mir_i8 : MIRType`
- `mir_i6 : MIRType`
- `mir_i32 : MIRType`
- `mir_i64 : MIRType`
- `mir_i128 : MIRType`
- `mir_isize : MIRType`
- `mir_f32 : MIRType`
- `mir_f64 : MIRType`
- `mir_lifetime : MIRType`
- `mir_raw_ptr_const : MIRType -> MIRType`
- `mir_raw_ptr_mut : MIRType -> MIRType`
- `mir_ref : MIRType -> MIRType`
- `mir_ref_mut : MIRType -> MIRType`
- `mir_slice : MIRType -> MIRType`
- `mir_str : MIRType`
- `mir_tuple : [MIRType] -> MIRType`
- `mir_u8 : MIRType`
- `mir_u6 : MIRType`
- `mir_u32 : MIRType`
- `mir_u64 : MIRType`
- `mir_u128 : MIRType`
- `mir_usize : MIRType`

Most of these types are straightforward mappings to the standard LLVM
and Java types. The one key difference is that arrays must have a fixed,
concrete size. Therefore, all analysis results are valid only under the
assumption that any arrays have the specific size indicated, and may not
hold for other sizes.

The `llvm_int` function takes an `Int` parameter indicating the variable's bit
width. For example, the C `uint16_t` and `int16_t` types correspond to
`llvm_int 16`. The C `bool` type is slightly trickier. A bare `bool` type
typically corresponds to `llvm_int 1`, but if a `bool` is a member of a
composite type such as a pointer, array, or struct, then it corresponds to
`llvm_int 8`. This is due to a peculiarity in the way Clang compiles `bool`
down to LLVM.  When in doubt about how a `bool` is represented, check the LLVM
bit
 by compiling your code with `clang -S -emit-llvm`.

LLVM types can also be specified in LLVM syntax directly by using the
`llvm_type` function.

- `llvm_type : String -> LLVMType`

For example, `llvm_type "i32"` yields the same result as `llvm_int 32`.

The most common use for creating fresh variables is to state that a
particular function should have the specified behaviour for arbitrary
initial values of the variables in question. Sometimes, however, it can
be useful to specify that a function returns (or stores, more about this
later) an arbitrary value, without specifying what that value should be.
To express such a pattern, you can also run `llvm_fresh_var` from
the post state (i.e., after `llvm_execute_func`).

## The SetupValue, JVMValue, and MIRValue Types

Many specifications require reasoning about both pure values and about
the configuration of the heap. The `SetupValue` type corresponds to
values that can occur during symbolic execution, which includes both
`Term` values, pointers, and composite types consisting of either of
these (both structures and arrays).

The `llvm_term`, `jvm_term`, and `mir_term` functions create a `SetupValue`,
`JVMValue`, or `MIRValue`, respectively, from a `Term`:

- `llvm_term : Term -> SetupValue`
- `jvm_term : Term -> JVMValue`
- `mir_term : Term -> MIRValue`

The value that these functions return will have an LLVM, JVM, or MIR type
corresponding to the Cryptol type of the `Term` argument. (For more information
on this, refer to the "Cryptol type correspondence" section.) If the type does
not have a Cryptol counterpart, the function will raise an error.

### Cryptol type correspondence

The `{llvm,jvm,mir}_fresh_var` functions take an LLVM, JVM, or MIR type as an
argument and produces a `Term` variable of the corresponding Cryptol type as
output. Similarly, the `{llvm,jvm,mir}_term` functions take a Cryptol `Term` as
input and produce a value of the corresponding LLVM, JVM, or MIR type as
output. This section describes precisely which types can be converted to
Cryptol types (and vice versa) in this way.

#### LLVM verification

The following LLVM types correspond to Cryptol types:

- `llvm_alias <name>`: Corresponds to the same Cryptol type as the type used
  in the definition of `<name>`.
- `llvm_array <n> <ty>`: Corresponds to the Cryptol sequence `[<n>][<cty>]`,
  where `<cty>` is the Cryptol type corresponding to `<ty>`.
- `llvm_int <n>`: Corresponds to the Cryptol word `[<n>]`.
- `llvm_struct_type [<ty_1>, ..., <ty_n>]` and `llvm_packed_struct [<ty_1>, ..., <ty_n>]`:
  Corresponds to the Cryptol tuple `(<cty_1>, ..., <cty_n>)`, where `<cty_i>`
  is the Cryptol type corresponding to `<ty_i>` for each `i` ranging from `1`
  to `n`.

The following LLVM types do _not_ correspond to Cryptol types:

- `llvm_double`
- `llvm_float`
- `llvm_pointer`

#### JVM verification

The following Java types correspond to Cryptol types:

- `java_array <n> <ty>`: Corresponds to the Cryptol sequence `[<n>][<cty>]`,
  where `<cty>` is the Cryptol type corresponding to `<ty>`.
- `java_bool`: Corresponds to the Cryptol `Bit` type.
- `java_byte`: Corresponds to the Cryptol `[8]` type.
- `java_char`: Corresponds to the Cryptol `[16]` type.
- `java_int`: Corresponds to the Cryptol `[32]` type.
- `java_long`: Corresponds to the Cryptol `[64]` type.
- `java_short`: Corresponds to the Cryptol `[16]` type.

The following Java types do _not_ correspond to Cryptol types:

- `java_class`
- `java_double`
- `java_float`

#### MIR verification

The following MIR types correspond to Cryptol types:

- `mir_array <n> <ty>`: Corresponds to the Cryptol sequence `[<n>][<cty>]`,
  where `<cty>` is the Cryptol type corresponding to `<ty>`.
- `mir_bool`: Corresponds to the Cryptol `Bit` type.
- `mir_char`: Corresponds to the Cryptol `[32]` type.
- `mir_i8` and `mir_u8`: Corresponds to the Cryptol `[8]` type.
- `mir_i16` and `mir_u16`: Corresponds to the Cryptol `[16]` type.
- `mir_i32` and `mir_u32`: Corresponds to the Cryptol `[32]` type.
- `mir_i64` and `mir_u64`: Corresponds to the Cryptol `[64]` type.
- `mir_i128` and `mir_u128`: Corresponds to the Cryptol `[128]` type.
- `mir_isize` and `mir_usize`: Corresponds to the Cryptol `[64]` type.
- `mir_tuple [<ty_1>, ..., <ty_n>]`: Corresponds to the Cryptol tuple
  `(<cty_1>, ..., <cty_n>)`, where `<cty_i>` is the Cryptol type corresponding
  to `<ty_i>` for each `i` ranging from `1` to `n`.

The following MIR types do _not_ correspond to Cryptol types:

- `mir_adt`
- `mir_f32`
- `mir_f64`
- `mir_ref` and `mir_ref_mut`
- `mir_raw_ptr_const` and `mir_raw_ptr_mut`
- `mir_slice`
- `mir_str`

## Executing

Once the initial state has been configured, the `{llvm,jvm,mir}_execute_func`
command specifies the parameters of the function being analyzed in terms
of the state elements already configured.

- `llvm_execute_func : [SetupValue] -> LLVMSetup ()`
- `jvm_execute_func : [JVMValue] -> JVMSetup ()`
- `mir_execute_func : [MIRValue] -> MIRSetup ()`

## Return Values

To specify the value that should be returned by the function being
verified use the `{llvm,jvm,mir}_return` command.

- `llvm_return : SetupValue -> LLVMSetup ()`
- `jvm_return : JVMValue -> JVMSetup ()`
- `mir_return : MIRValue -> MIRSetup ()`

## A First Simple Example (Revisited)

:::{warning}
This section is under construction!

See [the example's introduction](first-simple-example).
:::

(compositional-verification)=
## Compositional Verification

The primary advantage of the specification-based approach to
verification is that it allows for compositional reasoning. That is,
when proving properties of a given method or function, we can make use
of properties we have already proved about its callees rather than
analyzing them anew. This enables us to reason about much larger
and more complex systems than otherwise possible.

The `llvm_verify`, `jvm_verify`, and `mir_verify` functions return values of
type `CrucibleMethodSpec`, `JVMMethodSpec`, and `MIRMethodSpec`, respectively.
These values are opaque objects that internally contain both the information
provided in the associated `LLVMSetup`, `JVMSetup`, or `MIRSetup` blocks,
respectively, and the results of the verification process.

Any of these `MethodSpec` objects can be passed in via the third
argument of the `..._verify` functions. For any function or method
specified by one of these parameters, the simulator will not follow
calls to the associated target. Instead, it will perform the following
steps:

- Check that all `llvm_points_to` and `llvm_precond` statements
  (or the corresponding JVM or MIR statements) in the specification are
  satisfied.

- Update the simulator state and optionally construct a return value as
  described in the specification.

More concretely, building on the previous example, say we have a
doubling function written in terms of `add`:

:::{code-block} c
uint32_t dbl(uint32_t x) {
    return add(x, x);
}
:::

It has a similar specification to `add`:

:::{code-block} sawscript
let dbl_setup = do {
    x <- llvm_fresh_var "x" (llvm_int 32);
    llvm_execute_func [llvm_term x];
    llvm_return (llvm_term {{ x + x : [32] }});
};
:::

And we can verify it using what we've already proved about `add`:

:::{code-block} sawscript
llvm_verify m "dbl" [add_ms] false dbl_setup abc;
:::

In this case, doing the verification compositionally doesn't save
computational effort, since the functions are so simple, but it
illustrates the approach.

### Compositional Verification and Mutable Allocations

A common pitfall when using compositional verification is to reuse a
specification that underspecifies the value of a mutable allocation. In
general, doing so can lead to unsound verification, so SAW goes through great
lengths to check for this.

Here is an example of this pitfall in an LLVM verification. Given this C code:

::: c
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
### Compositional Verification and Mutable Global Variables

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

## Specifying Heap Layout

Most functions that operate on pointers expect that certain pointers
point to allocated memory before they are called. The `llvm_alloc`
command allows you to specify that a function expects a particular
pointer to refer to an allocated region appropriate for a specific type.

- `llvm_alloc : LLVMType -> LLVMSetup SetupValue`

This command returns a `SetupValue` consisting of a pointer to the
allocated space, which can be used wherever a pointer-valued
`SetupValue` can be used.

In the initial state, `llvm_alloc` specifies that the function
expects a pointer to allocated space to exist. In the final state, it
specifies that the function itself performs an allocation.

In LLVM, it's also possible to construct fresh pointers that do not
point to allocated memory (which can be useful for functions that
manipulate pointers but not the values they point to):

- `llvm_fresh_pointer : LLVMType -> LLVMSetup SetupValue`

The NULL pointer is called `llvm_null` in LLVM and `jvm_null` in
JVM:

- `llvm_null : SetupValue`
- `jvm_null : JVMValue`

One final, slightly more obscure command is the following:

- `llvm_alloc_readonly : LLVMType -> LLVMSetup SetupValue`

This works like `llvm_alloc` except that writes to the space
allocated are forbidden. This can be useful for specifying that a
function should take as an argument a pointer to allocated space that it
will not modify. Unlike `llvm_alloc`, regions allocated with
`llvm_alloc_readonly` are allowed to alias other read-only regions.

When using the experimental Java implementation, separate functions
exist for specifying that arrays or objects are allocated:

- `jvm_alloc_array : Int -> JavaType -> JVMSetup JVMValue` specifies an
array of the given concrete size, with elements of the given type.

- `jvm_alloc_object : String -> JVMSetup JVMValue` specifies an object
of the given class name.

The experimental MIR implementation also has a `mir_alloc` function, which
behaves similarly to `llvm_alloc`. `mir_alloc` creates an immutable reference,
but there is also a `mir_alloc_mut` function for creating a mutable reference:

- `mir_alloc : MIRType -> MIRSetup MIRValue`

- `mir_alloc_mut : MIRType -> MIRSetup MIRValue`

MIR tracks whether references are mutable or immutable at the type level, so it
is important to use the right allocation command for a given reference type.

In addition, MIR also has immutable and mutable raw pointers, written in Rust as
`*const T` and `*mut T` respectively. As far as SAW is concerned, they behave
similarly to references, and they can be created with `mir_alloc_raw_ptr_const`
and `mir_alloc_raw_ptr_mut` respectively.

- `mir_alloc_raw_ptr_const : MIRType -> MIRSetup MIRValue`

- `mir_alloc_raw_ptr_mut : MIRType -> MIRSetup MIRValue`

In low-level Rust code, it is possible to get a raw pointer into an allocation
of multiple values, do pointer arithmetic on it, and then read from or write to
various values within the allocation. The `crucible-mir` memory model keeps
track of these allocation sizes to check the validity of these pointer
operations. `mir_alloc_raw_ptr_const` and `mir_alloc_raw_ptr_mut` create
single-value allocations which don't allow for pointer arithmetic. To model
pointers which point to allocations containing multiple values, there are the
`mir_alloc_raw_ptr_const_multi` and `mir_alloc_raw_ptr_mut_multi` commands:

- `mir_alloc_raw_ptr_const_multi : Int -> MIRType -> MIRSetup MIRValue`

- `mir_alloc_raw_ptr_mut_multi : Int -> MIRType -> MIRSetup MIRValue`

The `Int` argument specifies how many values of the given type there are (*not*
the size in bytes). If `mir_alloc_raw_ptr_{const,mut}_multi n` is used in the
pre-state section of a specification (before `mir_execute_func`), it will create
an allocation of `n` values, with the pointer pointing to the first value in
that allocation. However, if used in the post-state section (after
`mir_execute_func`), the raw pointer `MIRValue` is able to be matched against a
raw pointer into a larger allocation produced by the function. The only
requirement is that the pointer points to a contiguous sequence of `n` values
within some allocation; the allocation is allowed to contain more values before
or after those `n` values.

## Specifying Heap Values

Pointers returned by `llvm_alloc`, `jvm_alloc_{array,object}`, or
`mir_alloc{,_mut,_ptr_const,_ptr_mut}` don't initially point to anything. So if
you pass such a pointer directly into a function that tried to dereference it,
symbolic execution will fail with a message about an invalid load. For some
functions, such as those that are intended to initialize data structures
(writing to the memory pointed to, but never reading from it), this sort of
uninitialized memory is appropriate. In most cases, however, it's more useful to
state that a pointer points to some specific (usually symbolic) value, which you
can do with the _points-to_ family of commands.

### LLVM heap values

LLVM verification primarily uses the `llvm_points_to` command:

- `llvm_points_to : SetupValue -> SetupValue -> LLVMSetup ()`
takes two `SetupValue` arguments, the first of which must be a pointer,
and states that the memory specified by that pointer should contain the
value given in the second argument (which may be any type of
`SetupValue`).

When used in the final state, `llvm_points_to` specifies that the
given pointer _should_ point to the given value when the function
finishes.

Occasionally, because C programs frequently reinterpret memory of one
type as another through casts, it can be useful to specify that a
pointer points to a value that does not agree with its static type.

- `llvm_points_to_untyped : SetupValue -> SetupValue ->
LLVMSetup ()` works like `llvm_points_to` but omits type
checking. Rather than omitting type checking across the board, we
introduced this additional function to make it clear when a type
reinterpretation is intentional. As an alternative, one
may instead use `llvm_cast_pointer` to line up the static types.

### JVM heap values

JVM verification has two categories of commands for specifying heap values.
One category consists of the `jvm_*_is` commands, which allow users to directly
specify what value a heap object points to. There are specific commands for
each type of JVM heap object:

- `jvm_array_is : JVMValue -> Term -> JVMSetup ()` declares that an array (the
  first argument) contains a sequence of values (the second argument).
- `jvm_elem_is : JVMValue -> Int -> JVMValue -> JVMSetup ()` declares that an
  array (the first argument) has an element at the given index (the second
  argument) containing the given value (the third argument).
- `jvm_field_is : JVMValue -> String -> JVMValue -> JVMSetup ()` declares that
  an object (the first argument) has a field (the second argument) containing
  the given value (the third argument).
- `jvm_static_field_is : String -> JVMValue -> JVMSetup ()` declares that a
  named static field (the first argument) contains the given value (the second
  argument). By default, the field name is assumed to belong to the same class
  as the method being specified. Static fields belonging to other classes can
  be selected using the `<classname>.<fieldname>` syntax in the first argument.

Another category consists of the `jvm_modifies_*` commands. Like the `jvm_*_is`
commands, these specify that a JVM heap object points to valid memory, but
unlike the `jvm_*_is` commands, they leave the exact value being pointed to as
unspecified. These are useful for writing partial specifications for methods
that modify some heap value, but without saying anything specific about the new
value.

- `jvm_modifies_array : JVMValue -> JVMSetup ()`
- `jvm_modifies_elem : JVMValue -> Int -> JVMSetup ()`
- `jvm_modifies_field : JVMValue -> String -> JVMSetup ()`
- `jvm_modifies_static_field : String -> JVMSetup ()`

### MIR heap values

MIR verification primarily uses the `mir_points_to` command:

- `mir_points_to : MIRValue -> MIRValue -> MIRSetup ()` takes two `MIRValue`
  arguments, the first of which must be a reference or raw pointer, and states
  that the memory specified by that reference or raw pointer should contain the
  value given in the second argument (which may be any type of `MIRValue`).

As a convenience, SAW also provides:

- `mir_ref_of : MIRValue -> MIRSetup MIRValue`
- `mir_ref_of_mut : MIRValue -> MIRSetup MIRValue`

which combine `mir_alloc`/`mir_alloc_mut` and `mir_points_to` into a single
operation.

Some low-level Rust code involves casting raw pointers, resulting in raw
pointers which point to values of a different type than what the raw pointer's
static type claims. This can be modeled in SAW using the `mir_cast_raw_ptr`
command:

- `mir_cast_raw_ptr : MIRValue -> MIRType -> MIRType` takes a raw pointer and a
  type, and returns a raw pointer to the same memory location and with the same
  mutability as the given pointer, but with the given type as the static pointee
  type instead.

Unlike in the LLVM backend, this does *not* allow for reinterpretation of
memory. If a raw pointer points to an allocation that is actually of type `T`,
the pointer can be cast and passed around and stored as a pointer to another
type, but it must be casted back to `*T` when it is actually dereferenced.
Accordingly, SAW enforces that `mir_points_to` can only be used on a non-casted
pointer, so that the value in the second argument matches the type passed to the
`mir_alloc_raw_ptr` that created the raw pointer in the first argument.
`mir_cast_raw_ptr` can be used, though, whenever some Rust signature is
expecting a pointer whose static pointee type does not match its "true" type at
runtime.

For raw pointers to contiguous sequences of multiple values, created by
`mir_alloc_raw_ptr_const_multi` and `mir_alloc_raw_ptr_mut_multi`, the
`mir_points_to_multi` command can be used to specify the multiple values.

- `mir_points_to_multi : MIRValue -> MIRValue -> MIRSetup ()`

The second argument must have a MIR array type, and it specifies the sequence of
pointed-to values as a MIR array. Specifically, if the first argument is a raw
pointer to a contiguous sequence of `n` values of type `ty`, the second argument
must have the MIR type `mir_array m ty` where `m <= n`. Note that the second
argument need not be constructed with `mir_array_value`; it can also be derived
from a fresh variable or a Cryptol sequence expression. Also note that the
pointed-to values are not (necessarily) the contents of an array in the actual
MIR semantics; their corresponding `MIRValue`s are just represented as an array
in SAWScript specs, for ease of conversion from Cryptol sequences.

## Working with Compound Types

The commands mentioned so far give us no way to specify the values of
compound types (arrays or `struct`s). Compound values can be dealt with
either piecewise or in their entirety.

- `llvm_elem : SetupValue -> Int -> SetupValue` yields a pointer to
an internal element of a compound value. For arrays, the `Int` parameter
is the array index. For `struct` values, it is the field index.

- `llvm_field : SetupValue -> String -> SetupValue` yields a pointer
to a particular named `struct` field, if debugging information is
available in the bitcode.

Either of these functions can be used with `llvm_points_to` to
specify the value of a particular array element or `struct` field.
Sometimes, however, it is more convenient to specify all array elements
or field values at once. The `llvm_array_value` and `llvm_struct_value`
functions construct compound values from lists of element values.

- `llvm_array_value : [SetupValue] -> SetupValue`
- `llvm_struct_value : [SetupValue] -> SetupValue`

To specify an array or struct in which each element or field is
symbolic, it would be possible, but tedious, to use a large combination
of `llvm_fresh_var` and `llvm_elem` or `llvm_field` commands.
However, the following function can simplify the common case
where you want every element or field to have a fresh value.

- `llvm_fresh_expanded_val : LLVMType -> LLVMSetup SetupValue`

The `llvm_struct_value` function normally creates a `struct` whose layout
obeys the alignment rules of the platform specified in the LLVM file
being analyzed. Structs in LLVM can explicitly be "packed", however, so
that every field immediately follows the previous in memory. The
following command will create values of such types:

- `llvm_packed_struct_value : [SetupValue] -> SetupValue`

C programs will sometimes make use of pointer casting to implement
various kinds of polymorphic behaviors, either via direct pointer
casts, or by using `union` types to codify the pattern. To reason
about such cases, the following operation is useful.

- `llvm_cast_pointer : SetupValue -> LLVMType -> SetupValue`

This function function casts the type of the input value (which must be a
pointer) so that it points to values of the given type.  This mainly
affects the results of subsequent `llvm_field` and `llvm_elem` calls,
and any eventual `points_to` statements that the resulting pointer
flows into.  This is especially useful for dealing with C `union`
types, as the type information provided by LLVM is imprecise in these
cases.

We can automate the process of applying pointer casts if we have debug
information avaliable:

- `llvm_union : SetupValue -> String -> SetupValue`

Given a pointer setup value, this attempts to select the named union
branch and cast the type of the pointer. For this to work, debug
symbols must be included; moreover, the process of correlating LLVM
type information with information contained in debug symbols is a bit
heuristic. If `llvm_union` cannot figure out how to cast a pointer,
one can fall back on the more manual `llvm_cast_pointer` instead.

In the experimental Java verification implementation, the following
functions can be used to state the equivalent of a combination of
`llvm_points_to` and either `llvm_elem` or `llvm_field`.

- `jvm_elem_is : JVMValue -> Int -> JVMValue -> JVMSetup ()` specifies
the value of an array element.

- `jvm_field_is : JVMValue -> String -> JVMValue -> JVMSetup ()`
specifies the name of an object field.

In the experimental MIR verification implementation, the following functions
construct compound values:

- `mir_array_value : MIRType -> [MIRValue] -> MIRValue` constructs an array
  of the given type whose elements consist of the given values. Supplying the
  element type is necessary to support length-0 arrays.
- `mir_enum_value : MIRAdt -> String -> [MIRValue] -> MIRValue` constructs an
  enum using a particular enum variant. The `MIRAdt` arguments determines what
  enum type to create, the `String` value determines the name of the variant to
  use, and the `[MIRValue]` list are the values to use as elements in the
  variant.

  See the "Finding MIR algebraic data types" section (as well as the "Enums"
  subsection) for more information on how to compute a `MIRAdt` value to pass
  to `mir_enum_value`.
- `mir_slice_value : MIRValue -> MIRValue`: see the "MIR slices" section below.
- `mir_slice_range_value : MIRValue -> Int -> Int -> MIRValue`: see the
  "MIR slices" section below.
- `mir_str_slice_value : MIRValue -> MIRValue`: see the "MIR slices" section
  below.
- `mir_str_slice_range_value : MIRValue -> Int -> Int -> MIRValue`: see the
  "MIR slices" section below.
- `mir_struct_value : MIRAdt -> [MIRValue] -> MIRValue` construct a struct
  with the given list of values as elements. The `MIRAdt` argument determines
  what struct type to create.

  See the "Finding MIR algebraic data types" section for more information on how
  to compute a `MIRAdt` value to pass to `mir_struct_value`.
- `mir_tuple_value : [MIRValue] -> MIRValue` construct a tuple with the given
  list of values as elements.

To specify a compound value in which each element or field is symbolic, it
would be possible, but tedious, to use a large number of `mir_fresh_var`
invocations in conjunction with the commands above. However, the following
function can simplify the common case where you want every element or field to
have a fresh value:

- `mir_fresh_expanded_value : String -> MIRType -> MIRSetup MIRValue`

The `String` argument denotes a prefix to use when generating the names of
fresh symbolic variables. The `MIRType` can be any type, with the exception of
reference types (or compound types that contain references as elements or
fields), which are not currently supported.

The following functions extract components of compound MIR values:

- `mir_elem_value : MIRValue -> Int -> MIRValue` takes an array value and an
  index, and returns the value in the array at that index.
- `mir_elem_ref : MIRValue -> Int -> MIRValue` takes a reference (or raw
  pointer) to an array, and an index, and returns a reference (resp. raw
  pointer) to the element in the array at that index.

Note that unlike `llvm_elem`, `mir_elem_ref` cannot be used to specify the value
of a specific index of an array reference without the whole array reference
already being initialized.

### MIR slices

Slices are a unique form of compound type that is currently only used during
MIR verification. Unlike other forms of compound values, such as arrays, it is
not possible to directly construct a slice. Instead, one must take a slice of
an existing reference value that points to the thing being sliced.

SAW currently supports taking slices of arrays and strings.

#### Array slices

The following commands are used to construct slices of arrays:

- `mir_slice_value : MIRValue -> MIRValue`: the SAWScript expression
  `mir_slice_value base` is equivalent to the Rust expression `&base[..]`,
  i.e., a slice of the entirety of `base`. `base` must be a reference to an
  array value (`&[T; N]` or `&mut [T; N]`), not an array itself. The type of
  `mir_slice_value base` will be `&[T]` (if `base` is an immutable reference)
  or `&mut [T]` (if `base` is a mutable reference).
- `mir_slice_range_value : MIRValue -> Int -> Int -> MIRValue`: the SAWScript
  expression `mir_slice_range_value base start end` is equivalent to the Rust
  expression `&base[start..end]`, i.e., a slice over a part of `base` which
  ranges from `start` to `end`. `base` must be a reference to an array value
  (`&[T; N]` or `&mut [T; N]`), not an array itself. The type of
  `mir_slice_value base` will be `&[T]` (if `base` is an immutable reference)
  or `&mut [T]` (if `base` is a mutable reference).

  `start` and `end` are assumed to be zero-indexed. `start` must not exceed
  `end`, and `end` must not exceed the length of the array that `base` points
  to.

As an example of how to use these functions, consider this Rust function, which
accepts an arbitrary slice as an argument:

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

Note that we are passing _references_ of arrays to `mir_slice_value` and
`mir_slice_range_value`. It would be an error to pass a bare array to these
functions, so the following specification would be invalid:

:::{code-block} sawscript
let f_fail_spec_ = do {
  let arr = mir_term {{ [1, 2, 3, 4, 5] : [5][32] }};

  mir_execute_func [mir_slice_value arr]; // BAD: `arr` is not a reference

  mir_return (mir_term {{ 3 : [32] }});
};
:::

Note that The `mir_slice_range_value` function must accept bare `Int` arguments
to specify the lower and upper bounds of the range. A consequence of this
design is that it is not possible to create a slice with a symbolic length. If
this limitation prevents you from using SAW, please file an issue [on
GitHub](https://github.com/GaloisInc/saw-script/issues).

#### String slices

In addition to slices of arrays (i.e., of type `&[T]`), SAW also supports
slices of strings (i.e., of type `&str`) through the following commands:

- `mir_str_slice_value : MIRValue -> MIRValue`: the SAWScript expression
  `mir_str_slice_value base` is equivalent to the Rust expression `&base[..]`,
  i.e., a slice of the entirety of `base`. `base` must be a reference to an
  array of bytes (`&[u8; N]` or `&mut [u8; N]`), not an array itself. The type
  of `mir_str_slice_value base` will be `&str` (if `base` is an immutable
  reference) or `&mut str` (if `base` is a mutable reference).
- `mir_str_slice_range_value : MIRValue -> Int -> Int -> MIRValue`: the
  SAWScript expression `mir_slice_range_value base start end` is equivalent to
  the Rust expression `&base[start..end]`, i.e., a slice over a part of `base`
  which ranges from `start` to `end`. `base` must be a reference to an array of
  bytes (`&[u8; N]` or `&mut [u8; N]`), not an array itself. The type of
  `mir_slice_value base` will be `&str` (if `base` is an immutable reference)
  or `&mut str` (if `base` is a mutable reference).

  `start` and `end` are assumed to be zero-indexed. `start` must not exceed
  `end`, and `end` must not exceed the length of the array that `base` points
  to.

One unusual requirement about `mir_str_slice_value` and
`mir_str_slice_range_value` is that they require the argument to be of type
`&[u8; N]`, i.e., a reference to an array of bytes. This is an artifact of the
way that strings are encoded in Cryptol. The following Cryptol expressions:

- `"A"`
- `"123"`
- `"Hello World"`

Have the following types:

- `[1][8]`
- `[3][8]`
- `[11][8]`

This is because Cryptol strings are syntactic shorthand for sequences of bytes.
The following Cryptol expressions are wholly equivalent:

- `[0x41]`
- `[0x31, 0x32, 0x33]`
- `[0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x57, 0x6f, 0x72, 0x6c, 0x64]`

These represent the strings in the extended ASCII character encoding. The
Cryptol sequence type `[N][8]` is equivalent to the Rust type `[u8; N]`, so the
requirement to have something of type `&[u8; N]` as an argument reflects this
design choice.

Note that `mir_str_slice_value <u8_array_ref>` is _not_ the same thing as
`mir_slice_value <u8_array_ref>`, as the two commands represent different types
of Rust values. While both commands take a `<u8_array_ref>` as an argument,
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

### MIR `Vec`s

[`Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html) is a commonly used
data type in the Rust standard library. `Vec` values can be created from array
values in MIR specifications with the following command:

- `mir_vec_of : String -> MIRType -> MIRValue -> MIRSetup MIRValue`

The `String` argument is used as a prefix for naming the internal symbolic
variables created as part of the `Vec` struct (think of it just as a name you
give to the `Vec` variable). The `MIRType` argument is the element type of the
`Vec`. The `MIRValue` argument is the contents of the `Vec`, which must be a MIR
array value whose element type matches the `MIRType` argument. Note that this
could either be created with `mir_array_value` or obtained from a `Term` like a
fresh variable or a Cryptol sequence expression.

`Vec` is just a regular struct and not a special language construct, so
technically you could write specifications for `Vec`s just using the primitive
MIR specification commands (in fact, this is what `mir_vec_of` does internally).
However, you would need to explicitly specify all the internal details and
invariants of `Vec`, and that can get quite messy. Therefore, this command
exists for convenience reasons.

### Finding MIR algebraic data types

We collectively refer to MIR `struct`s and `enum`s together as _algebraic data
types_, or ADTs for short. ADTs have identifiers to tell them apart, and a
single ADT declaration can give rise to multiple identifiers depending on how
the declaration is used. For example:

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

This program as a single `struct` declaration `S`, which is used in the
functions `f` and `g`. Note that `S`'s declaration is _polymorphic_, as it uses
type parameters, but the uses of `S` in `f` and `g` are _monomorphic_, as `S`'s
type parameters are fully instantiated. Each unique, monomorphic instantiation
of an ADT gives rise to its own identifier. In the example above, this might
mean that the following identifiers are created when this code is compiled with
`mir-json`:

- `S<u8, u16>` gives rise to `example/abcd123::S::_adt456`
- `S<u32, u64>` gives rise to `example/abcd123::S::_adt789`

The suffix `_adt<number>` is autogenerated by `mir-json` and is typically
difficult for humans to guess. For this reason, we offer a command to look up
an ADT more easily:

- `mir_find_adt : MIRModule -> String -> [MIRType] -> MIRAdt` consults the
  given `MIRModule` to find an algebraic data type (`MIRAdt`). It uses the given
  `String` as an identifier and the given MIRTypes as the types to instantiate
  the type parameters of the ADT. If such a `MIRAdt` cannot be found in the
  `MIRModule`, this will raise an error.

Note that the `String` argument to `mir_find_adt` does not need to include the
`_adt<num>` suffix, as `mir_find_adt` will discover this for you. The `String`
is expected to adhere to the identifier conventions described in the "Running a
MIR-based verification" section. For instance, the following two lines will
look up `S<u8, u16>` and `S<u32, u64>` from the example above as `MIRAdt`s:

:::{code-block} sawscript
m <- mir_load_module "example.linked-mir.json";

let s_8_16  = mir_find_adt m "example::S" [mir_u8,  mir_u16];
let s_32_64 = mir_find_adt m "example::S" [mir_u32, mir_u64];
:::

Note that there is also a command to look up ADTs by their full, _mangled_
identifiers that include the `_adt<num>` suffix:

- `mir_find_mangled_adt : MIRModule -> String -> MIRAdt`

Note that unlike `mir_find_adt`, `mir_find_mangled_adt` lacks `[MirType]`
arguments, as the type information is already encoded into the mangled
identifier.

It is recommended to use `mir_find_adt` over `mir_find_mangled_adt` whenever
possible, as mangled identifiers can change easily when recompiling Rust code.
`mir_find_mangled_adt` is generally only needed to work around limitations in
what `mir_find_adt` can look up. For instance, SAW currently does not have a
way to look up instantiations of ADTs that use const generics, so
`mir_find_mangled_adt` is the only way to look up such ADTs at present.

The `mir_adt` command (for constructing a struct type), `mir_struct_value` (for
constructing a struct value), and `mir_enum_value` (for constructing an enum
value) commands in turn take a `MIRAdt` as an argument.

#### Enums

In addition to taking a `MIRAdt` as an argument, `mir_enum_value` also takes a
`String` representing the name of the variant to construct. The variant name
should be a short name such as `"None"` or `"Some"`, and not a full identifier
such as `"core::option::Option::None"` or `"core::option::Option::Some"`. This
is because the `MIRAdt` already contains the full identifiers for all of an
enum's variants, so SAW will use this information to look up a variant's
identifier from a short name. Here is an example of using `mir_enum_value` in
practice:

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

Note that `mir_enum_value` can only be used to construct a specific variant. If
you need to construct a symbolic enum value that can range over many potential
variants, use `mir_fresh_expanded_value` instead.

#### Lifetimes

Rust ADTs can have both type parameters as well as _lifetime_ parameters. The
following Rust code declares a lifetime parameter `'a` on the struct `S`, as
well on the function `f` that computes an `S` value:

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

### Bitfields

SAW has experimental support for specifying `struct`s with bitfields, such as
in the following example:

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

- `llvm_points_to_bitfield : SetupValue -> String -> SetupValue -> LLVMSetup ()`

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

Both `llvm_points_to_bitfield` and `enable_lax_loads_and_stores` are
experimental commands, so these also require using `enable_experimental` before
they can be used.

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

## Global variables

SAW supports verifying LLVM and MIR specifications involving global variables.

### LLVM global variables

Mutable global variables that are accessed in a function must first be allocated
by calling `llvm_alloc_global` on the name of the global.

- `llvm_alloc_global : String -> LLVMSetup ()`

This ensures that all global variables that might influence the function are
accounted for explicitly in the specification: if `llvm_alloc_global` is
used in the precondition, there must be a corresponding `llvm_points_to`
in the postcondition describing the new state of that global. Otherwise, a
specification might not fully capture the behavior of the function, potentially
leading to unsoundness in the presence of compositional verification. (For more
details on this point, see the [Compositional Verification and Mutable Global
Variables](#compositional-verification-and-mutable-global-variables) section.)

Immutable (i.e. `const`) global variables are allocated implicitly, and do not
require a call to `llvm_alloc_global`.

Pointers to global variables or functions can be accessed with
`llvm_global`:

- `llvm_global : String -> SetupValue`

Like the pointers returned by `llvm_alloc`, however, these aren't
initialized at the beginning of symbolic -- setting global variables may
be unsound in the presence of [compositional
verification](#compositional-verification).

To understand the issues surrounding global variables, consider the following C
code:

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

One might initially write the following specifications for `f` and `g`:

<!-- This matches intTests/test0036_globals/test-signed-fail.saw -->
:::{code-block} sawscript
m <- llvm_load_module "./test.bc";

f_spec <- llvm_verify m "f" [] true (do {
    y <- llvm_fresh_var "y" (llvm_int 32);
    llvm_execute_func [llvm_term y];
    llvm_return (llvm_term {{ 1 + y : [32] }});
}) abc;

g_spec <- llvm_llvm_verify m "g" [] true (do {
    z <- llvm_fresh_var "z" (llvm_int 32);
    llvm_execute_func [llvm_term z];
    llvm_return (llvm_term {{ 2 + z : [32] }});
}) abc;
:::

If globals were always initialized at the beginning of verification,
both of these specs would be provable. However, the results wouldn't
truly be compositional. For instance, it's not the case that `f(g(z)) ==
z + 3` for all `z`, because both `f` and `g` modify the global variable
`x` in a way that crosses function boundaries.

To deal with this, we can use the following function:

- `llvm_global_initializer : String -> SetupValue` returns the value
  of the constant global initializer for the named global variable.

Given this function, the specifications for `f` and `g` can make this
reliance on the initial value of `x` explicit:

<!-- This matches intTests/test0036_globals/test-signed.saw -->
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
the beginning of verification. This specification is now safe for
compositional verification: SAW won't use the specification `f_spec`
unless it can determine that `x` still has its initial value at the
point of a call to `f`. This specification also constrains `y` to prevent
signed integer overflow resulting from the `x + y` expression in `f`,
which is undefined behavior in C.

(mir-static-items)=
### MIR static items

Rust's static items are the MIR version of global variables. A reference to a
static item can be accessed with the `mir_static` function. This function takes
a `String` representing a static item's identifier, and this identifier is
expected to adhere to the naming conventions outlined in the "Running a
MIR-based verification" section:

- `mir_static : String -> MIRValue`

References to static values can be initialized with the `mir_points_to`
command, just like with other forms of references. Immutable static items
(e.g., `static X: u8 = 42`) are initialized implicitly in every SAW
specification, so there is no need for users to do so manually. Mutable static
items (e.g., `static mut Y: u8 = 27`), on the other hand, are _not_ initialized
implicitly, and users must explicitly pick a value to initialize them with.

The `mir_static_initializer` function can be used to access the initial value
of a static item in a MIR program. Like with `mir_static`, the `String`
supplied as an argument must be a valid identifier:

- `mir_static_initializer : String -> MIRValue`.

As an example of how to use these functions, here is a Rust program involving
static items:

:::{code-block} rust
// statics.rs
static     S1: u8 = 1;
static mut S2: u8 = 2;

pub fn f() -> u8 {
    // Reading a mutable static item requires an `unsafe` block due to
    // concurrency-related concerns. We are only concerned about the behavior
    // of this program in a single-threaded context, so this is fine.
    let s2 = unsafe { S2 };
    S1 + s2
}
:::

We can write a specification for `f` like so:

:::{code-block} sawscript
// statics.saw
enable_experimental;

let f_spec = do {
  mir_points_to (mir_static "statics::S2")
                (mir_static_initializer "statics::S2");
  // Note that we do not initialize S1, as immutable static items are implicitly
  // initialized in every specification.

  mir_execute_func [];

  mir_return (mir_term {{ 3 : [8] }});
};

m <- mir_load_module "statics.linked-mir.json";

mir_verify m "statics::f" [] false f_spec z3;
:::

In order to use a specification involving mutable static items for
compositional verification, it is required to specify the value of all mutable
static items using the `mir_points_to` command in the specification's
postconditions. For more details on this point, see the [Compositional
Verification and Mutable Global
Variables](#compositional-verification-and-mutable-global-variables) section.

## Preconditions and Postconditions

Sometimes a function is only well-defined under certain conditions, or
sometimes you may be interested in certain initial conditions that give
rise to specific final conditions. For these cases, you can specify an
arbitrary predicate as a precondition or post-condition, using any
values in scope at the time.

- `llvm_precond : Term -> LLVMSetup ()`
- `llvm_postcond : Term -> LLVMSetup ()`
- `llvm_assert : Term -> LLVMSetup ()`
- `jvm_precond : Term -> JVMSetup ()`
- `jvm_postcond : Term -> JVMSetup ()`
- `jvm_assert : Term -> JVMSetup ()`
- `mir_precond : Term -> MIRSetup ()`
- `mir_postcond : Term -> MIRSetup ()`
- `mir_assert : Term -> MIRSetup ()`

These commands take `Term` arguments, and therefore cannot describe the values
of pointers. The "assert" variants will work in either pre- or post-conditions,
and are useful when defining helper functions that, e.g., provide datastructure
invariants that make sense in both phases.  The `{llvm,jvm,mir}_equal` commands
state that two values should be equal, and can be used in either the initial or
the final state.

- `llvm_equal : SetupValue -> SetupValue -> LLVMSetup ()`
- `jvm_equal : JVMValue -> JVMValue -> JVMSetup ()`
- `mir_equal : MIRValue -> MIRValue -> MIRSetup ()`

The use of `{llvm,jvm,mir}_equal` can also sometimes lead to more efficient
symbolic execution when the predicate of interest is an equality.

## Assuming specifications

Normally, a `MethodSpec` is the result of both simulation and proof of
the target code. However, in some cases, it can be useful to use a
`MethodSpec` to specify some code that either doesn't exist or is hard
to prove. The previously-mentioned [`assume_unsat`
tactic](#finishing-proofs-without-external-solvers) omits proof but does not prevent
simulation of the function. To skip simulation altogether, one can use
one of the following commands:


- `llvm_unsafe_assume_spec : LLVMModule -> String -> LLVMSetup () -> TopLevel CrucibleMethodSpec`
- `jvm_unsafe_assume_spec : JavaClass -> String -> JVMSetup () -> TopLevel JVMMethodSpec`
- `mir_unsafe_assume_spec : MIRModule -> String -> MIRSetup () -> TopLevel MIRSpec`

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

Ghost state variables do not initially have any particluar type, and can
store data of any type. Given an existing ghost variable the following
functions can be used to specify its value:

- `llvm_ghost_value : Ghost -> Term -> LLVMSetup ()`
- `jvm_ghost_value  : Ghost -> Term -> JVMSetup  ()`
- `mir_ghost_value  : Ghost -> Term -> MIRSetup  ()`

These can be used in either the pre state or the post state, to specify the
value of ghost state either before or after the execution of the function,
respectively.

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
`alloc_init : LLVMType -> Term -> LLVMSetup SetupValue`.

`alloc_init ty v` returns a `SetupValue` consisting of a pointer to memory
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
`ptr_to_fresh : String -> LLVMType -> LLVMSetup (Term, SetupValue)`.

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
parameters of kind `#`, representing e.g. the sizes of input sequences.
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
