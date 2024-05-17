# Revision history for saw-client

## 1.1.1 -- 2024-05-16

* Add support for Python 3.12

## 1.1.0 -- 2024-02-05

* Add Python bindings for SAW's experimental MIR verification support:

  * The `mir_load_module` function loads a MIR JSON file into SAW.
  * The `mir_verify` function performs verification of a MIR function.
  * The `mir_find_adt` function looks up an algebraic data type (ADT) name in a
    MIR module.
  * The `mir_assume` function assumes a specification for a MIR function without
    performing any verification.
  * The `saw_client.mir` module contains utility functions for constructing
    MIR types.

  For more information about how SAW's MIR verification support works in
  general, see the `mir_*` commands documented in the [SAW
  manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md).
* The `array()` function now takes an additional `element_type` argument, which
  defaults to `None`. If constructing a MIR array with no elements, then the
  `element_type` must be specified. Otherwise, this argument is optional.
* The `struct()` function now takes an additional `mir_adt` argument, which
  defaults to `None`. If building a MIR struct, this `mir_adt` argument is
  required. Passing a `mir_adt` argument when building an LLVM struct will raise
  an error.
* Add a `tuple_value()` function for constructing MIR tuples. Using this
  function with LLVM or JVM verification will raise an error.
* Add `slice_value()` and `slice_range()` functions for constructing MIR slices.
  Using these functions with LLVM or JVM verification will raise an error.
* The `proclaim` function (which is the Python counterpart to to
  `{llvm,jvm,mir}_assert` in SAWScript) is no longer deprecated.
* Add a `proclaim_f` function. This behaves like the `proclaim` function, except
  that it takes a `cry_f`-style format string as an argument. That is,
  `proclaim_f(...)` is equivalent to `proclaim(cry_f(...))`.
* Add a `fresh_expanded` function that creates a value entirely populated by
  fresh symbolic variables. For compound types such as structs or arrays, this
  will explicitly set each field or element to contain a fresh symbolic
  variable. This function is currently only supported with LLVM and MIR
  verification, and using this function with JVM verification will raise an
  error.
* Add an `enum()` function for constructing MIR enum values.
* The `create_ghost_variable()` and `ghost_value()` functions are now supported
  with JVM and MIR verification.

## 1.0.1 -- YYYY-MM-DD

* Add `solver_cache.py` implementing an interface for interacting with SAW
  solver cache databases.

## 1.0.0 -- 2023-06-26

* The v1.0.0 release is made in tandem with the SAW 1.0 release. See the
  SAW 1.0 release notes for relevant SAW changes.
* Add a `set_option` command to `saw_client` that allows enabling and disabling
  global SAW options. For example, SAWScript's `enable_lax_pointer_ordering` is
  equivalent to `set_option(LaxPointerOrdering(), True)` in `saw-client.
  `LaxPointerOrdering`, as well as all other possible options, can be imported
  from the `saw_client.option` module.
* Add a `points_to_bitfield` command that allows specifying fields of structs
  that contain bitfields. The caveats described in the Bitfields section of the
  SAW manual also apply to Python. Notably, one must use
  `set_option(LaxLoadsAndStores(), True)` in order for `points_to_bitfield` to
  work as expected. `points_to_bitfield` is only supported for LLVM (and not
  JVM) verification.
* Added two new commands, `eval_int` and `eval_bool`, that evaluate Cryptol
  expressions to Python integers or booleans.


## 0.9.0 -- 2021-11-19

* v0.9 release
