// cross-function.cpp — Exception propagation across function boundaries.
//
// Compile to bitcode:
//   clang++ -emit-llvm -c -O0 cross-function.cpp -o cross-function.bc
//
// Then run the lowering pass:
//   ../exception-lower cross-function.bc -o cross-function-lowered.bc
//
// Tests that the invoke→call+check transformation correctly propagates
// error sentinels through a multi-level call chain.

#include <cstdint>

// Level 0: the leaf function that actually throws.
int leaf(int x) {
  if (x < 0)
    throw -1;
  return x;
}

// Level 1: calls leaf(), does NOT catch — exception propagates up.
// In the lowered form, the invoke of leaf becomes call+check, and if
// the error flag is set this function should also return the sentinel.
int level1(int x) {
  int v = leaf(x);
  return v + 10;
}

// Level 2: same pattern — no catch, just propagation.
int level2(int x) {
  int v = level1(x);
  return v + 100;
}

// Level 3: the top-level caller that finally catches.
int caller(int x) {
  try {
    return level2(x);
  } catch (int e) {
    return e;  // returns the original -1
  }
}

// --- Entry point for standalone execution ---
#ifdef STANDALONE
#include <cstdio>
int main() {
  std::printf("caller(5)  = %d\n", caller(5));   // 115
  std::printf("caller(-1) = %d\n", caller(-1));   // -1
  return 0;
}
#endif
