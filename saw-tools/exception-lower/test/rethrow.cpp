// rethrow.cpp — Catch, modify state, then rethrow.
//
// Compile to bitcode:
//   clang++ -emit-llvm -c -O0 rethrow.cpp -o rethrow.bc
//
// Then run the lowering pass:
//   ../exception-lower rethrow.bc -o rethrow-lowered.bc
//
// Tests that `resume` instructions are correctly lowered to
// re-setting the error flag and returning the error sentinel.

#include <cstdint>

// Global counter visible to SAW — records how many times we rethrowed.
static int rethrow_count = 0;

int fragile(int x) {
  if (x == 0)
    throw -1;
  return 100 / x;
}

// Catches, increments a counter, then rethrows.
// In the lowered form this should:
//   1. Detect error from fragile()
//   2. Clear error flag (__cxa_begin_catch equivalent)
//   3. Increment rethrow_count
//   4. Re-set error flag (resume → re-set flag + return sentinel)
int middleware(int x) {
  try {
    return fragile(x);
  } catch (...) {
    rethrow_count++;
    throw;  // rethrow — becomes `resume` in LLVM IR
  }
}

// Top-level caller that finally handles the exception.
int top_caller(int x) {
  try {
    return middleware(x);
  } catch (int e) {
    return e;  // returns the original -1
  }
}

int get_rethrow_count() {
  return rethrow_count;
}

// --- Entry point for standalone execution ---
#ifdef STANDALONE
#include <cstdio>
int main() {
  std::printf("top_caller(10) = %d\n", top_caller(10));   // 10
  std::printf("top_caller(0)  = %d\n", top_caller(0));    // -1
  std::printf("rethrow_count  = %d\n", get_rethrow_count()); // 1
  return 0;
}
#endif
