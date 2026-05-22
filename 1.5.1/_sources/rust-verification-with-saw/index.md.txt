# Rust Verification with SAW

This tutorial introduces SAW's Rust/MIR verification capabilities.
After completing this tutorial, you will be able to:

- Use `saw-rustc` and `cargo-saw-build` to extract SAW-ready MIR from Rust
- Use SAW's MIR capabilities to verify code that utilizes references and
  compound data types (i.e. `struct`s and `enum`s)
- Write proofs _compositionally_, even when the subtleties of mutable references
  are involved
- Verify code that utilizes _static items_

Additionally, you will step through the process of verifying an implementation
of the Salsa20 stream cipher against a Cryptol reference specification, showing
how SAW's MIR capabilities may be used on a more realistic codebase.

You can download {download-dir}`the tutorial files <code>`.

```{toctree}
:maxdepth: 2
:caption: Contents

introduction
prerequisites
about-mir-json
saw-basics
reference-types
compound-data-types
overrides-and-compositional-verification
static-items
case-study-salsa20
a-final-word
```
