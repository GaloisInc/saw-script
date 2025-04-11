Test the `llvm_ffi_setup` command for verifying Cryptol `foreign`
functions.

These test cases are mostly from the test suite for the Cryptol FFI, but
with Cryptol implementations of each function provided as well so that
we can verify them with SAW. Some functions are changed or removed since
SAW doesn't support Cryptol's Float types right now. There are also some
additional tests for the more tricky parts of the llvm_ffi_setup
implementation.
