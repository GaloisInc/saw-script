# Revision history for saw-remote-api

## next -- TBA

* Add remote API support for SAW's experimental MIR verification support:

  * The `SAW/MIR/load module` command loads a MIR JSON file into SAW.
  * The `SAW/MIR/verify` command performs verification of a MIR function.
  * The `SAW/MIR/find ADT` command looks up an algebraic data type (ADT) name in
    a MIR module.
  * The `SAW/MIR/assume` command assumes a specification for a MIR function
    without performing any verification.

  See the [remote API
  documentation](https://github.com/GaloisInc/saw-script/blob/master/saw-remote-api/docs/SAW.rst#sawmirload-module-command)
  for more detailed APIs for each of these commands. For more information about
  how SAW's MIR verification support works in general, see the `mir_*` commands
  documented in the [SAW
  manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md).
* The API for `"array"` `setup value`s now has an `"element type"` field. For
  LLVM verification, this field is optional. For MIR verification, this field
  is required if the `"elements"` value is empty and optional if the
  `"elements"` value is non-empty.
* The old `"tuple"` `setup value` has been renamed to `"struct"`. This better
  reflects its intended purpose of representing struct values. There is now a
  new `"tuple"` `setup value` that is only used to represent MIR tuples.
* The API for `"struct"` `setup value`s now has a `"MIR ADT"` field. For
  MIR verification, this field is required. For LLVM and JVM verification,
  this field must be `null`, or else an error will be raised.
* Add a `"fresh expanded"` `setup value` that denotes a value entirely
  populated by fresh symbolic variables. For compound types such as structs or
  arrays, this will explicitly set each field or element to contain a fresh
  symbolic variable. This is currently only supported with LLVM and MIR
  verification, and using this with JVM verification will raise an error.
* Add `"slice"` and `"slice range"` `setup value`s representing slices in MIR
  verification. Attempting to use these in LLVM or JVM verification will raise
  an error.
* The `SAW/create ghost variable` command and the associated
  `ghost variable value` value are now supported with JVM and MIR verification.

## 1.0.0 -- 2023-06-26

* The v1.0.0 release is made in tandem with the SAW 1.0 release. See the
  SAW 1.0 release notes for relevant SAW changes.
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
* Introduced new methods `SAW/eval int` and `SAW/eval bool` that allow the
  evaluation of Cryptol expressions into Python values.

## 0.9.0 -- 2021-11-19

* v0.9 release
