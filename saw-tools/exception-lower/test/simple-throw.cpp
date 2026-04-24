// simple-throw.cpp — minimal C++ exception test case.
//
// Compile to bitcode:
//   clang++ -emit-llvm -c -O0 simple-throw.cpp -o simple-throw.bc
//
// Then run the lowering pass:
//   ../exception-lower simple-throw.bc -o simple-throw-lowered.bc

#include <cstdio>

int may_throw(int x) {
  if (x < 0)
    throw -1;
  return x * 2;
}

int safe_caller(int x) {
  try {
    return may_throw(x);
  } catch (int e) {
    std::printf("caught: %d\n", e);
    return e;
  }
}

int main() {
  std::printf("result: %d\n", safe_caller(5));
  std::printf("result: %d\n", safe_caller(-3));
  return 0;
}
