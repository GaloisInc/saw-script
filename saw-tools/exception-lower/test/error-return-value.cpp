// error-return-value.cpp — Golden reference: hand-written lowered form.
//
// This file is the expected output pattern of the exception-lower pass.
// It uses explicit error-return values instead of C++ exceptions, matching
// the transformation described in ../README.md.
//
// Compile to bitcode:
//   clang++ -emit-llvm -c -O0 error-return-value.cpp -o error-return-value.bc
//
// Use this as a reference when comparing against lowered output from the
// pass applied to simple-throw.cpp (or other test inputs).

#include <cstdint>

// ---------- Thread-local error state (matches pass output) ----------

struct ErrorState {
  bool     flag;        // true when an exception is "in flight"
  int      type_id;     // discriminator for exception type
  int64_t  value;       // the exception payload (cast to int64_t)
};

// In real lowered output these would be thread-local globals.
// For verification purposes a single static instance suffices.
static ErrorState __exc_state = {false, 0, 0};

// Sentinel return value used to signal "exception in flight".
static const int ERROR_SENTINEL = -2147483647;  // INT_MIN + 1

// ---------- Lowered equivalents of simple-throw.cpp functions ----------

// Lowered form of:
//   int may_throw(int x) {
//     if (x < 0) throw -1;
//     return x * 2;
//   }
int may_throw_lowered(int x) {
  if (x < 0) {
    // __cxa_allocate_exception + __cxa_throw →
    //   store error info, set flag, return sentinel
    __exc_state.flag    = true;
    __exc_state.type_id = 1;         // int type
    __exc_state.value   = -1;        // the thrown value
    return ERROR_SENTINEL;
  }
  return x * 2;
}

// Lowered form of:
//   int safe_caller(int x) {
//     try { return may_throw(x); }
//     catch (int e) { return e; }
//   }
int safe_caller_lowered(int x) {
  int result = may_throw_lowered(x);

  // invoke→call + error-flag check
  if (__exc_state.flag) {
    // landingpad → read error type/value
    int caught_type  = __exc_state.type_id;
    int64_t caught_val = __exc_state.value;

    // __cxa_begin_catch → clear flag
    __exc_state.flag = false;

    if (caught_type == 1) {
      // Matched: catch (int e)
      return static_cast<int>(caught_val);
    }

    // No match → resume (re-set flag, return sentinel)
    __exc_state.flag = true;
    return ERROR_SENTINEL;
  }

  return result;
}

// ---------- Cross-function propagation lowered form ----------

// Lowered form of a non-catching intermediate function:
//   int level1(int x) { int v = leaf(x); return v + 10; }
int level1_lowered(int x) {
  int v = may_throw_lowered(x);

  // Check error flag after call
  if (__exc_state.flag)
    return ERROR_SENTINEL;  // propagate error

  return v + 10;
}

// ---------- Accessors for SAW verification ----------

bool get_error_flag() {
  return __exc_state.flag;
}

int get_error_value() {
  return static_cast<int>(__exc_state.value);
}

void reset_error_state() {
  __exc_state.flag    = false;
  __exc_state.type_id = 0;
  __exc_state.value   = 0;
}

// --- Entry point for standalone execution ---
#ifdef STANDALONE
#include <cstdio>
int main() {
  reset_error_state();
  std::printf("safe_caller_lowered(5)  = %d\n", safe_caller_lowered(5));   // 10
  reset_error_state();
  std::printf("safe_caller_lowered(-3) = %d\n", safe_caller_lowered(-3));  // -1

  reset_error_state();
  std::printf("level1_lowered(5)  = %d\n", level1_lowered(5));   // 20
  reset_error_state();
  std::printf("level1_lowered(-3) = %d\n", level1_lowered(-3));  // sentinel

  return 0;
}
#endif
