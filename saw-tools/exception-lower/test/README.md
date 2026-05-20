# exception-lower developer harness

Developer-facing fixtures for the `exception-lower` LLVM pass.  Each
C++ source here exercises a different EH pattern.  The shell harness
builds them, runs the pass, and (optionally) disassembles the output
for inspection.

This directory is **not** part of the saw-script integration-test suite;
it is intended for developers actively working on the pass.  The
post-lowering shape is verified end-to-end by the integration test
[`intTests/test_exception_lower/`](../../../intTests/test_exception_lower/),
which does not require the pass binary to be built.

## Test cases

| File                    | Pattern tested                                    |
|-------------------------|---------------------------------------------------|
| `simple-throw.cpp`      | Basic throw/catch within one function              |
| `nested-try-catch.cpp`  | Inner and outer try/catch with different types     |
| `rethrow.cpp`           | Catch → modify state → rethrow (`resume` lowering) |
| `cross-function.cpp`    | Exception propagating through multiple call levels |

## Running

```bash
# Compile and lower all fixtures:
./run-tests.sh

# Clean generated artifacts:
./run-tests.sh --clean
```

### Prerequisites

- `clang++` with `-emit-llvm` support
- `exception-lower` tool built in `../build/`
- `llvm-dis` (optional, for inspecting lowered IR)

## How the lowered form works

The pass replaces exception constructs with an explicit error-state struct:

```
ErrorState { flag: bool, type_id: int, value: int64 }
```

- **throw** → set flag + store type/value + return sentinel
- **invoke** → call + check flag + branch
- **catch** → read type/value + clear flag
- **resume** → re-set flag + return sentinel

A hand-written reference of this pattern (used by the integration test)
lives in
[`intTests/test_exception_lower/error-return-value.cpp`](../../../intTests/test_exception_lower/error-return-value.cpp).
