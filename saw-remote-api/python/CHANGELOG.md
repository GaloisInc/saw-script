# Revision history for saw-client

## 0.9.1 -- YYYY-MM-DD

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


## 0.9.0 -- 2021-11-19

* v0.9 release
