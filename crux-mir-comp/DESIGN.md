## General design

The workflow for compositional verification with `crux-mir-comp` is as follows:

 1. The user writes a symbolic test `f_test` for a function `f`.  Running the
    test ensures that `f` satisfies some property.
 2. The user converts `f_test` into a *spec function* `f_spec` that returns a
    `MethodSpec` representing the same property.  (Currently the user must do
    the conversion manually, but the process is mechanical and designed to be
    automatable using a Rust procedural macro.)
 3. The user writes a symbolic test `g_test` for a function `g` which calls
    `f`, using `f_spec().enable()` to override `f` with its `MethodSpec` for
    the duration of `g_test`.

For example:

```Rust
fn f(x: (u8, u8)) -> (u8, u8) {
    (x.1, x.0)
}

#[crux::test]
fn f_test() {
    let x = <(u8, u8)>::symbolic("x");
    crucible_assume!(x.0 > 0);

    let y = f(x);

    crucible_assert!(y.1 > 0);
}

fn f_spec() -> MethodSpec {
    let x = <(u8, u8)>::symbolic("x");
    crucible_assume!(x.0 > 0);

    let mut msb = MethodSpecBuilder::new(f);
    msb.add_arg(&x);
    msb.gather_assumes();
    let y = <(u8, u8)>::symbolic("result");

    crucible_assert!(y.1 > 0);

    msb.set_return(&y);
    msb.gather_asserts();
    msb.finish()
}

#[crux::test]
fn use_f() {
    f_spec().enable();

    let a = u8::symbolic("a");
    let b = u8::symbolic("b");
    crucible_assume!(0 < a && a < 10);
    let (c, d) = f((a, b));
    crucible_assert!(0 < d);    // Passes; postcondition includes `y.1 > 0`
    crucible_assert!(d < 10);   // Fails; satisfied by `f` but not by `f_spec`
}
```

The `MethodSpecBuilder` API used in spec functions is designed to reuse as much
of the symbolic testing infrastructure as possible.  This is what allows for
the mechanical translation of tests to spec functions.  Symbolic variables
created with `symbolic()` turn into "fresh variables" in the `MethodSpec`, and
assumptions/assertions established with `crucible_assume!`/`crucible_assert!`
turn into pre/postconditions.  (Note that proof goals established during the
spec function are discarded after being collected into the `MethodSpec`, as
otherwise they would cause verification to fail.)


## Memory

In general, the argument values that the spec function provides to
`msb.add_arg()` are converted to patterns (`SetupValue`s), and the actual
arguments provided to the resulting `MethodSpec` override are matched against
those patterns to establish an assignment of values to the `MethodSpec`'s
symbolic variables.  When the arguments contain references (or raw pointers),
this process is applied recursively to the target of the reference.  In the
spec function, when `add_arg` encounters a reference `r`, it adds a new
allocation to the `MethodSpec`, converts the value `*r` to a pattern (just as
it would for a top-level argument), and generates a `PointsTo` condition
asserting that the allocation's contents must match the pattern.  Then, when
running the `MethodSpec` override, the actual value and the pattern of each
`PointsTo` are matched just as actual argument values are matched to the
argument patterns.

The handling of references proceeds recursively, with the effect that the
`MethodSpec` records the complete shape of all memory accessible through the
provided arguments, and thus calls to the `MethodSpec` override will only
succeed if the actual arguments point to memory of the same shape.

There is no distinction between heap-allocated and stack-allocated memory, so
spec functions can use references to the stack for simplicity:
```Rust
let x = u8::symbolic("x");
msb.add_arg(& &x);
```
while callers of the `MethodSpec` override can provide any valid reference for
that argument.

To conservatively model the function's behavior, the spec function *clobbers*
(overwrites with fresh symbolic values) all mutable memory accessible through
the arguments.  The postcondition can then constrain the new values to specify
the effect of the function on the memory that it modifies.  Only mutable
locations are clobbered; a location is considered mutable if it is accessible
through a mutable reference or if it is wrapped in the `UnsafeCell` type.
(`UnsafeCell` is the low-level "interior mutability" primitive used to
implement the standard `Cell` and `RefCell` types.)  All immutable locations
are left unchanged, so there is no need to specify explicitly that they retain
their prior values.  Note that `*const` raw pointers are treated as being
mutable, since in some situations it is legal for unsafe code to cast a
`*const` pointer to `*mut` and then write through it.

Pointer arithmetic on a pointer `p` can allow a function to access not just
`*p` but also `*p.add(1)`, `*p.sub(1)`, and so on.  `crux-mir`'s model of
pointer arithmetic allows this whenever `p` is a pointer to an array element.
To handle this soundly, first, the `MethodSpecBuilder` records the number of
accessible elements before and after each pointer `p` that it encounters, and
generates `PointsTo` constraints for each such element.  Second, when the
override is called, the actual pointer that gets matched against `p` must have
at least as many elements before and after, and all those elements must match
as described by the `PointsTo`s.  For example, if spec function provides a
pointer to the first element of a two-element array, then the caller of the
override can provide a pointer to the first element of a three-element array or
a pointer to the third element of a four-element array, but not a pointer to a
single item or to the last element of an array, as neither of the latter
provides access to a second element at `*p.add(1)`.


## Globals

`crux-mir-comp` has minimal support for globals, sufficient for soundness but
not for any significant reasoning.  Each test function is required to begin
with a call to `clobber_globals()`, which overwrites every mutable global
location with a fresh symbolic value, in order to ensure that the property
being tested holds for all possible global values.  And `MethodSpec` overrides
clobber all mutable global locations when called, as a conservative
overapproximation of the behavior of the function.  Currently, preconditions
and postconditions cannot mention globals, so there is no way to constrain the
arbitrary symbolic values introduced by clobbering.

As with memory accessible through references, only the mutable portions of
globals are clobbered.  Rust does not permit changing the values of immutable
`static`s (outside `UnsafeCell`) by any means, so clobbering globals does not
affect these values.  In particular, lookup tables (such as the tables used in
implementations of some cryptographic algorithms) are usually declared as
immutable and thus always retain their initial values.


## Cryptol

It is possible to import Cryptol expressions into symbolic Rust test cases to
help write specifications (e.g., if you want to check that a Rust implementation
matches a Cryptol specification).  This is done by using the `cryptol!` macro
defined in the `crucible` crate.  Here's an example illustrating how to
import a Cryptol function `myCryFun` defined in Cryptol module `SomeCryMod`,
and bind it as the Rust function `myRustFun`:

```Cryptol
module SomeCryMod where
  f: [8] -> [32]
  f x = 0 # x
```
```Rust
use crucible::*;
cryptol! {
    path "SomeCryMod";
    pub fn myRustFun(x: u8) -> u32 = r"myCryFun";
}
```

Тhe `path` component of the macro specifies a Cryptol module,
the string after the `=` is a Cryptol expression, and the rest of the
declaration specifies how to invoke evaluating the Cryptol expression from
Rust.  If the declaration contains `const` generics, then the Cryptol expression
is specified as a format string which may refer to the values of the const
generic parameters in curly braces (literal curly braces need to be escaped
as a double curly brace).  Here's an example of how to use a function with
const generics:
```Cryptol``
module Cryptol where
  sum : {n, a} (fin n, Eq a, Ring a) => [n]a -> a
  sum = foldl (+) zero
```
```Rust
extern crate crucible;
use crucible::*;
cryptol! {
    path "Cryptol";
    pub fn f<const N: usize>(x: &[u8]) -> u8 = r"sum`{{{N},[8]}}";
}
```

It is important that the type of the Cryptol expression is compatible
with the type of the declared Rust function, according to the following
rules:

  * The Cryptol type may have only numeric type parameters
  * The first parameters of the Rust function should correspond to the
    numeric type parameters of the Cryptol expression; they should be
    of basic Rust numeric types (e.g., `usize`)
  * Symbolic expressions may *not* be used as arguments corresponding to
    numeric type parameters.
  * References are transparently dereferenced
  * The remaining parameters to the Rust function should correspond to the
    parameters in the Cryptol type as follows:
      * Cryptol's `Bit` is represented as Rust's `bool`
      * A Cryptol sequence of length `n` may be represented as a Rust
        array of length `n`.
      * In the parameters of the Rust function, Cryptol sequences may also
        be represented as reference to slices.  The length of the slice should
        match the length of the Cryptol sequence, which is checked dynamically.
      * Cryptol `Bit` sequences of lengths corresponding to Rust's basic
        numeric types may also be represented with those types
        (e.g., `[8]` may be represented with `u8` or `i8`).
      * Cryptol tuples are represented as Rust tuples.


## Current limitations

* Only one specification can be provided at a time for each function.  There is
  no mechanism for providing multiple specifications for the same function and
  allowing the prover to choose the most appropriate override for each call
  site.

* Error reporting currently works by simply calling `error`, which provides
  very unfriendly error messages for users.

* Reasoning about functions that read or write mutable global variables is not
  yet supported.

* There is no automation yet for converting symbolic tests into spec functions.
  However, the `MethodSpecBuilder` API is designed to make this conversion
  straightforward.
