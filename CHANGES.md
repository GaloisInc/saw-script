# Unreleased version

## New Features

SAW now includes experimental support for verifying Java code using JDK 9 or
later. Verifying Java code that only uses primitive data types is known to work
well, but code that imports certain classes (e.g., `String`) is known to suffer
from issues documented
[here](https://github.com/GaloisInc/crucible/issues/641).

When verifying Java code, the path to Java can be specified with the new
`--java-bin-dirs`/`-b` command-line option. Alternatively, if
`--java-bin-dirs` is not set, then SAW searches the `PATH` to find Java.
When the path to Java is known, SAW can automatically add system-related
JAR files to the JAR path, which eliminates the need to manually specify
these files with `-j`.

SAWScript includes two new functions, `llvm_struct_type` and
`llvm_packed_struct_type`, for constructing an LLVM struct type from a list
of other LLVM types. This is not to be confused with the existing `llvm_struct`
function, which takes a string as an argument and returns the corresponding
alias type (which is often, but not necessarily, defined as a struct type).
To avoid confusion, a new `llvm_alias` function has been introduced, and
`llvm_struct` is now a synonym for `llvm_alias`. The `llvm_struct` function
continues to be available for now.

# Version 0.7

## New Features

SAW can now use the ABC prover as an external process in addition to the
linked-in version. This change is in preparation for removing the
linked-in version in a future release. This change has several parts:

* The new proof tactics `w4_abc_verilog` and `w4_abc_smtlib2` allow
  using ABC to discharge proof goals using either Verilog or SMT-Lib2 as
  the intermediate file format, respectively.
* The new `offline_verilog` tactic writes a proof goal in the subset of
  Verilog supported by ABC, which can allow the use of custom ABC
  commands to discharge it.
* The new `w4_offline_smtlib2` writes a proof goal in SMT-Lib2 syntax
  using What4 instead of SBV.
* The new `write_verilog` command will write a `Term` to a file in
  Verilog syntax from the top level of a script.
* The new `write_smtlib2_w4` command will write a `Term` to a file in
  SMT-Lib2 syntax from the top level of a script, using What4 instead of
  SBV.
* The new proof tactics `sbv_abc`, `sbv_boolector`, `sbv_cvc4`,
  `sbv_mathsat`, `sbv_yices`, `sbv_z3`, `sbv_unint_cvc4`,
  `sbv_unint_yices`, and `sbv_unint_z3` are now aliases for the same
  tactics without the `sbv_` prefixes in preparation for making the
  unprefixed tactics refer to the What4 versions of the same
  functionality.

Java verification using the Crucible symbolic execution engine is now
more flexible and performant.

* The new `jvm_array_is` command specifies the entire contents of an
  array together.
* The new `jvm_field_is` command allows disambiguation by type for
  fields of the same name but different types.
* JVM method names can be disambiguated using type descriptors.
* JVM constructors can be referred to by the name `<init>`.
* Error messages in JVM verification are significantly more helpful.

These changes, and various internal performance improvements, mean that
the ECDSA verification example included with SAW now runs in around 5
minutes on a modern laptop.

New features exist to summarize any verifications performed with SAW.
The `summarize_verification` command will print a list of all functions
or methods verified or assumed, and all lemmas proved with commands such
as `prove`. These summaries include the status (verified or assumed) of
each item along with the provers used to complete the proof. The `-s
<filename>` flag will instruct SAW to automatically write a summary to
the given file, and the `-f <format>` flag will instruct SAW to use
either a human-readable (`pretty`) format or JSON (`json`) for
consumption by other tools.

An experimental RPC server for SAW now exists, which provides an
alternative to SAWScript for controlling SAW execution. A client library
for interacting with the server from Python exists
[here](https://github.com/GaloisInc/argo/tree/master/python).

Verification of x86 code called from LLVM is now more flexible. The
`add_x86_preserved_reg` command can add a specific register to the set
that is assumed to be callee-saved, and path satisfiability checking is
now performed when passing `True` as the fifth argument to
`crucible_llvm_verify_x86`.

The new `cryptol_add_path` command adds a directory to the search path
used when loading Cryptol modules (and following imports within
explicitly-loaded modules).

New, shorter names are available for all LLVM commands starting with
the `crucible_` prefix. The new names use the `llvm_` prefix instead.
The top-level function `crucible_llvm_verify` is now `llvm_verify`,
and `crucible_llvm_unsafe_assume_spec` is `llvm_unsafe_assume_spec`.
The old names are still supported for now. The in-REPL documentation
(`:? <command>`) gives the new name for each command.

Shorter names are available for some saw-script types: `CrucibleSetup`
is now `LLVMSetup`, `CrucibleMethodSpec` is now simply `LLVMSpec`, and
`JVMMethodSpec` is `JVMSpec`. The old type names are still supported
for backward compatibility.


## Bug Fixes

* Catch more exceptions at the REPL (issues #138, #560, #745, and #814).
* Ensure global memory is immutable in x86 verification.
* Fix path sat checking (issues #683 and #723).

* Closed issues #61, #138, #158, #162, #212, #215, #265, #314, #319,
  #399, #412, #422, #439, #456, #544, #560, #562, #683, #686, #719,
  #723, #745, #814, #844, #845, #856, #866, #874, #888, #901, #902,
  #904, #911, #920, #936, #937, #945, and #957.

# Version 0.6

## New Features

* Adedd experimental support for _compositional extraction_.
  Previously, `crucible_llvm_extract` and similar functions could
  translate very simple imperative functions into `Term` models but
  analysis of more complex programs typically required verification of
  equivalence to Cryptol specifications. Now, the
  `crucible_llvm_compositional_extract` function allows extraction of
  any function that can be specified using a `CrucibleSetup` block of the
  sort used for `crucible_llvm_verify`. In addition, this extraction can
  be _compositional_, preserving the call structure that exists in the
  original program instead of inlining everything.

* Added experimental support for interactive offline proofs using Coq.
  The `write_coq_term` function and `offline_coq` tactic will export the
  associated `Term` to a file in Gallina syntax. This file can be
  imported into a Coq file that can do arbitrarily complex interactive
  proofs.

* Added experimental support for arrays of symbolic size. The new
  `crucible_array_alloc` function specifies the existence of an
  allocated array where the size is given by its `Term` argument. The
  new `crucible_points_to_array_prefix` function specifies that the
  given pointer points to (the prefix of) a symbolic array value of
  a given symbolic size.

* Improved x86 verification capabilities. Verification scripts for x86
  functions can now process functions with mutable globals and function
  calls (which are currently inlined), and can use proof scripts to
  discharge proof obligations.

* Added a new `llvm_sizeof` primitive, which works similarly to the
  `sizeof` operator in C.

* Added support for the `llvm.fshl.i32` funnel shift intrinsic.

* Added experimental support for _verification summaries_. These
  summaries list all verifications performed within a script in a
  concise way that can track arbitrarily complex proof orchestrations.
  Future releases will include more information in these summaries, and
  more textual explanation of the assumptions made during each proof.

## Other Changes

* Made small improvements to documentation and error messages
  throughout.

* Improved the performance of expression hashing (closing #674).

* Updated to include Cryptol 2.9.1 and all the associated changes.

## Bug Fixes

* Fixed handling of jumps in x86 verification.

* Fixed matching for points-to and return values for x86.

* Closed issues #140, #195, #225, #226, #387, #538, #542, #543, #556,
  #635, #640, #642, #674, #691, #693, #698, #699, #700, #701, #702,
  #704, #706, #707, #709, #720, #721, #730, #742, #744, #763, #768,
  #773, #783, #785, #789, #782, #803, #807, and #815.

# Version 0.5

## New Features

* Added experimental support for basic, non-compositional verification
  of x86 machine code for use in conjunction with LLVM verification.

        crucible_llvm_verify_x86 :
          LLVMModule -> String -> String ->
          [(String, Int)] -> Bool -> CrucibleSetup () ->
          TopLevel CrucibleMethodSpec

  The first argument specifies the LLVM module containing the _caller_.
  The second and third specify the ELF file name and symbol name of the
  function to be verifier. The fourth specifies the names and sizes (in
  bytes) of global variables to initialize, and the fifth whether to
  perform path satisfiability checking. The last argument is the LLVM
  specification of the calling context against which to verify the
  function.

* Added support for using the SMT theory of arrays in the LLVM memory
  model. In some cases, this can significantly improve performance.

        enable_smt_array_memory_model : TopLevel ()
        disable_smt_array_memory_model : TopLevel ()

* Added support for specifying alignment in LLVM allocations. The
  `crucible_alloc_aligned` and `crucible_alloc_readonly_aligned`
  functions allocate read-write and read-only memory regions,
  respectively, with the specified alignment (in bytes).

* Added a conditional points-to function,
  `crucible_conditional_points_to`, that allows an LLVM function to
  conditionally modify memory, leaving it in its previous state
  (potentially uninitialized) when the condition is false.

* Added several new options:

    * New functions `enable_what4_hash_consing` and
      `disable_what4_hash_consing` to enable or disable hash consing to
      increase sub-formula sharing during symbolic execution.

    * New functions `enable_crucible_assert_then_assume` and
      `disable_crucible_assert_then_assume` to control whether
      predicates are assumed after asserting them during symbolic
      execution. The default is now to not assume them, whereas
      previously they were assumed.

    * New command-line option `--no-color` to print an ASCII logo
      without ANSI color or Unicode.

## Performance Improvements

* Improved performance of the LLVM memory model.

* Improved performance of bitvector operations during symbolic execution.

* Improved performance of rewriting SAWCore terms.

## Bug Fixes

* Fixed SBV interface to fail more gracefully when it cannot find the
  solver executable.

* Fixed SMT-Lib export negation issues.

Fixes issues #286, #489, #491, #564, #580, #583, #585, #586, #587, #590,
 #592, #594, #597, #598, #602, #603, #612, #613, #622, #626, #633, #638,
 #639, and #647.

# Version 0.4

* Fixed a long-standing soundness issue (#30) in compositional
  verification of LLVM programs. Previously, a specification for a
  function that neglected to mention an effect that the function in fact
  caused could be successfully verified. When verifying a caller of that
  function, only the effects mentioned in the specification would be
  used. The fix for this issue may break some proof scripts: any pointer
  mentioned using `crucible_points_to` in the initial state of a
  specification but not in the final state will be assigned a final
  value of "invalid", and any subsequent reads from the pointer will
  fail. To fix this issue, make sure that every specification you use
  provides a final value for every pointer it touches (which in many
  cases will be the same as its initial value).

* Added an experimental command, `llvm_boilerplate`, that emits skeleton
  function specifications for every function defined in an LLVM module.
  The additional `crucible_llvm_array_size_profile` command can be used
  to refine the results of `llvm_boilerplate` based on the array sizes
  used by calls that arise from a call to the named top-level function.

* Added support for using the symbolic execution profiler available in
  Crucible. The `enable_crucible_profiling` command causes profiling
  information to be written to the given directory. This can then be
  visualized using the rendering code available
  [here](https://github.com/GaloisInc/sympro-ui).

* Added proof tactics to use Yices (`w4_unint_yices`) and CVC4
  (`w4_unint_cvc4`) through the What4 backend instead of SBV.

* Modified the messages emitted for failed points-to assertions to be in
  terms of LLVM values.

* Added support for using the SMT array memory model to reason about the
  LLVM heap. The `enable_smt_array_memory_model` command enables it for
  all future proofs.

* LLVM bitcode format support is improved. Versions 3.5 to 9.0
  are known to be mostly well-supported. We consider parsing failures
  with any version newer than 3.5 to be a bug, so please report them on
  [GitHub](https://github.com/GaloisInc/saw-script/issues/new).

* New experimental model counting commands `sharpSAT` and `approxmc`
  bind to the external tools of the same name. These were mistakenly
  listed as included in 0.3.

* Built against Cryptol 2.8.0.

* Improved error messages in general.

* Fixed various additional bugs, including #211, #455, #479, #484, #493,
  #496, #511, #521, #522, #534, #563

# Version 0.3

* Java and LLVM verification has been overhauled to use the new Crucible
  symbolic execution engine. Highlights include:

    * New `crucible_llvm_verify` and `crucible_llvm_extract` commands
      replace `llvm_verify` and `llvm_extract`, with a different
      structure for specification blocks.

    * LLVM verification tracks undefined behavior more carefully and has
      a more sophisicated memory model. See the
      [manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md#specification-based-verification)
      for more.

    * New, experimental `crucible_jvm_verify` and
      `crucible_java_extract` commands will eventually replace
      `java_verify` and `java_extract`. For the moment, the former two
      are enabled with the `enable_experimental` command and the latter
      two are enabled with `enable_deprecated`.

    * More flexible specification language allows convenient description
      of functions that allocate memory, return arbitrary values, expect
      explicit aliasing, work with NULL pointers, cast between pointers
      and integers, or work with opaque pointers.

    * Ghost state is supported in LLVM verification, allowing reasoning
      about certain complex or unavailable code.

    * Verification of LLVM works for a larger subset of the language,
      which particularly improves support for C++.

* LLVM bitcode format support is greatly improved. Versions 3.5 to 7.0
  are known to be mostly well-supported. We consider parsing failures
  with any version newer than 3.5 to be a bug, so please report them on
  [GitHub](https://github.com/GaloisInc/saw-script/issues/new).

* Greatly improved error messages throughout.

* Built against Cryptol 2.7.0.

* New model counting commands `sharpSAT` and `approxmc` bind to the
  external tools of the same name.

* New proof script commands allow multiple goals and related proof
  tactics. See the
  [manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md#multiple-goals).

* Can be built with Docker, and will be available on DockerHub.

* Includes an Emacs mode.

# Version 0.2-dev

* Released under the 3-clause BSD license

* Major improvements to the Java and LLVM verification infrastructure,
  as described in more detail [here](doc/java-llvm/java-llvm.md):
    * Major refactoring and polish to `java_verify` and `java_symexec`
    * Major refactoring and polish to `llvm_verify` and `llvm_symexec`
    * Fixed soundness bug in `llvm_verify` treatment of heap
      modifications
    * Fixed soundness bug related to `java_assert` and `llvm_assert`
    * Support for branch satisfiability checking to be configured
    * Support for some types of allocation in `java_verify`, enabled
      with `java_allow_alloc`
    * Improved support for LLVM structs (including the `llvm_struct`
      type for `llvm_verify`)
    * Support for non-scalar return values in `java_verify` and
      `java_symexec`
    * Support for using `java_ensure_eq` on fields of return value
    * Access to safety conditions in `java_symexec` and `llvm_symexec`
    * New primitives `llvm_assert_eq` and `java_assert_eq`

* Some changes to the SAWScript language:
    * Conditional expressions including the keywords `if`, `then`, and
      `else`, and the new constants `true` and `false`
    * New `eval_int` and `eval_bool` functions to expose Cryptol bit
      vectors and `Bit` values as `Int` and `Bool` values in SAWScript
    * Pattern matching for tuples
    * Improvements to pretty printing, including: `set_base` and
      `set_ascii` commands to control the formatting of values; a `show`
      function to convert a value to a string without printing it; and
      the ability to use `print` or `show` instead of
      `llvm_browse_module` and `java_browse_class`
    * New built-in functions for processing lists

* New proof backends:
    * A new `rme` proof tactic, based on the
      [Reed-Muller Expansion](https://en.wikipedia.org/wiki/Reed%E2%80%93Muller_expansion)
      normal form for propositional formulas. This tactic is
      particularly efficient for dealing with polynomials over Galois
      fields, as used in AES, for instance.

* Linked against the latest Cryptol code, which includes the following
  changes since release 2.3.0:
    * An extended prelude with more Haskell-like functions
    * Better, more portable seeding for `random`
    * Performance improvements for symbolically executing tables of
      constant values
    * Performance improvements for type checking large constants

* Internal improvements:
    * Simplified Cryptol to SAWCore translation
    * Improved performance of Cryptol to SAWCore translation for
      recursive functions
    * Updated bitcode parser to support some of the changes in LLVM 3.7
    * Many bug fixes
    * Many code cleanups
