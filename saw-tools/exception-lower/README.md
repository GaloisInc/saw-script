# exception-lower

A standalone LLVM pass that lowers C++ exception-handling constructs (the
Itanium EH ABI) into explicit error-flag control flow.  The resulting
bitcode can then be verified by SAW, which does not model stack unwinding.

## Building

Requires LLVM 14 or later and CMake ≥ 3.16.

```bash
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
cmake --build .
```

If LLVM is installed in a non-standard location, point CMake at it:

```bash
cmake .. -DLLVM_DIR=/path/to/llvm/lib/cmake/llvm
```

## Usage

```bash
# Lower exception constructs in a bitcode file:
./exception-lower input.bc -o output.bc

# The tool also accepts LLVM text IR (.ll) as input.
./exception-lower input.ll -o output.bc
```

## Transformation Summary

The pass replaces the following constructs:

| Original construct         | Replacement                                         |
|----------------------------|-----------------------------------------------------|
| `__cxa_allocate_exception` | Allocate an error struct                            |
| `__cxa_throw`              | Store error type/value in thread-local, return sentinel |
| `invoke`                   | `call` + check error flag + conditional branch      |
| `landingpad`               | Read error type from thread-local                   |
| `__cxa_begin_catch`        | Read and clear active exception                     |
| `__cxa_end_catch`          | No-op (removed)                                     |
| `resume`                   | Re-set error flag, return sentinel                  |

## Testing

Compile a C++ test file to bitcode, run the pass, then inspect the output:

```bash
clang++ -emit-llvm -c -O0 test/simple-throw.cpp -o test/simple-throw.bc
./exception-lower test/simple-throw.bc -o test/simple-throw-lowered.bc
llvm-dis test/simple-throw-lowered.bc -o - | less
```
