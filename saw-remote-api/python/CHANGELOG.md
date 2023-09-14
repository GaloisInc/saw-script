# Revision history for saw-client

## next -- TBA

* Add Python bindings for SAW's experimental MIR verification support:

  * The `mir_load_module` function loads a MIR JSON file into SAW.
  * The `mir_verify` function performs verification of a MIR function.
  * The `mir_find_adt` function looks up an algebraic data type (ADT) name in a
    MIR module.

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
