// nested-try-catch.cpp — Nested try/catch blocks.
//
// Compile to bitcode:
//   clang++ -emit-llvm -c -O0 nested-try-catch.cpp -o nested-try-catch.bc
//
// Then run the lowering pass:
//   ../exception-lower nested-try-catch.bc -o nested-try-catch-lowered.bc
//
// Tests that the pass correctly handles multiple landingpad instructions
// and nested invoke→call+check transformations.

#include <cstdint>

// Error codes used in the lowered version for comparison.
static const int ERR_RANGE   = -1;
static const int ERR_LOGIC   = -2;
static const int ERR_UNKNOWN = -99;

// Throws different exception types depending on the input.
int inner_may_throw(int x) {
  if (x < 0)
    throw ERR_RANGE;       // "range error"
  if (x > 1000)
    throw static_cast<long>(ERR_LOGIC);  // different type → outer catch
  return x + 1;
}

// Nested try/catch: inner catches int, outer catches everything.
int nested_caller(int x) {
  try {
    try {
      return inner_may_throw(x);
    } catch (int e) {
      // Inner handler: only catches int exceptions.
      return e;
    }
  } catch (...) {
    // Outer handler: catches anything that escapes the inner block
    // (e.g. the long exception).
    return ERR_UNKNOWN;
  }
}

// --- Entry point for standalone execution ---
#ifdef STANDALONE
#include <cstdio>
int main() {
  std::printf("nested_caller(5)    = %d\n", nested_caller(5));    // 6
  std::printf("nested_caller(-3)   = %d\n", nested_caller(-3));   // -1
  std::printf("nested_caller(2000) = %d\n", nested_caller(2000)); // -99
  return 0;
}
#endif
