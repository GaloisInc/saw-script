# Revision history for saw-remote-api

## 0.9.2 -- 2022-05-09

* Introduced new methods `SAW/eval int` and `SAW/eval bool` that allow the
  evaluation of Cryptol expressions into Python values.

## 0.9.1 -- 2021-12-21

* `SAW/set option`'s `"option"` parameter is now allowed to be `"What4 eval"`,
  which controls whether to enable or disable What4 translation for SAWCore
  expressions during Crucible symbolic execution.
* `SAW/set option`'s `"option"` parameter is now allowed to be
  `"lax loads and stores"`, which controls whether to enable or disable relaxed
  validity checking for memory loads and stores in Crucible.
* Specifications now have additional `pre points to bitfield` and
  `post points to bitfield` fields, each of which is a list of "points-to"
  relationships pertaining to structs that contain bitfields. If not specified,
  these will default to empty lists. Bitfields are only meaningful for LLVM
  verification, so JVM specifications must leave these lists empty. Attempting
  to provide a non-empty list for either of these fields in a JVM specification
  will result in an error.


## 0.9.0 -- 2021-11-19

* v0.9 release
