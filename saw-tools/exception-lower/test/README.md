# exception-lower test suite

Integration tests for the `exception-lower` LLVM pass.  Each test case
exercises a different C++ exception-handling pattern and verifies that the
lowering transformation produces correct error-return control flow.

## Test cases

| File                    | Pattern tested                                    |
|-------------------------|---------------------------------------------------|
| `simple-throw.cpp`      | Basic throw/catch within one function              |
| `nested-try-catch.cpp`  | Inner and outer try/catch with different types     |
| `rethrow.cpp`           | Catch → modify state → rethrow (`resume` lowering) |
| `cross-function.cpp`    | Exception propagating through multiple call levels |
| `error-return-value.cpp`| Golden reference: hand-written lowered form        |

## SAW verification

`verify-lowered.saw` verifies the golden reference and (once the pass is
implemented) the actual lowered output:

- Success path: function returns correct value when no exception.
- Error path: function returns the caught value (or sentinel) when an
  exception is thrown.

## Running

```bash
# Compile and lower all test cases:
./run-tests.sh

# Also run SAW verification on the golden reference:
./run-tests.sh --verify

# Clean generated artifacts:
./run-tests.sh --clean
```

### Prerequisites

- `clang++` with `-emit-llvm` support
- `exception-lower` tool built from the parent directory
- `llvm-dis` (optional, for inspecting lowered IR)
- `saw` (only needed with `--verify`)

## How the lowered form works

The pass replaces exception constructs with an explicit error-state struct:

```
ErrorState { flag: bool, type_id: int, value: int64 }
```

- **throw** → set flag + store type/value + return sentinel
- **invoke** → call + check flag + branch
- **catch** → read type/value + clear flag
- **resume** → re-set flag + return sentinel

See `error-return-value.cpp` for a complete hand-written example of this
pattern applied to the `simple-throw.cpp` test case.
