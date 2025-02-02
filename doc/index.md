# SAW Documentation

Welcome to the Software Analysis Workbench (SAW)!

If you are a new SAW user:

- [**LLVM/Java Verification with SAW**](llvm-java-verification-with-saw/index)
  introduces the core ideas of using SAW to verify LLVM/Java programs.
  This is the fastest way to get started with SAW for most use-cases.
- [**Rust Verification with SAW**](rust-verification-with-saw/index) introduces
  SAW's experimental support for Rust/MIR verification.
  If you would like to be introduced to SAW at the cutting-edge, this is the
  right place to start (the LLVM/Java material is _not_ prerequisite).

If you are looking for SAW/SAWScript reference materials:

- The [**SAW User Manual**](saw-user-manual/index) is an attempt at
  comprehensive user-level documentation of SAW's features.
  If the tutorials above don't introduce something you've encountered while
  reading or writing SAWScript, it is worth searching the manual to see if it is
  covered there.

If you encounter any bugs, please [open an
issue](https://github.com/GaloisInc/saw-script/issues) following the
[contributing
guidelines](https://github.com/GaloisInc/saw-script/blob/master/CONTRIBUTING.md#issue-tracking).

:::{toctree}
:hidden:

llvm-java-verification-with-saw/index
rust-verification-with-saw/index
saw-user-manual/index
:::
