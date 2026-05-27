// error-return-value.c -- hand-written "golden" form of the IR produced
// by the saw-tools/exception-lower pass.
//
// This file mirrors the post-lowering shape: throws are replaced with a
// thread-local error-flag store + sentinel return, catches become flag
// checks, and unhandled paths re-set the flag.  Verifying this file in SAW
// pins down the contract the pass is expected to satisfy, independently of
// whether the pass itself has been built and run.
//
// Written as plain C so that there is no name-mangling, no `extern "C"`
// wrappers, and no `static_cast`.  No standard headers are used so that
// the bitcode can be cross-compiled with `--target=x86_64-pc-linux-gnu`
// on systems that have no libc/libc++ for that target.

struct ErrorState {
    _Bool     flag;
    int       type_id;
    long long value;
};

// A single static instance suffices for verification purposes.
static struct ErrorState __exc_state = {0, 0, 0};

// Sentinel return value used to signal "exception in flight".
static const int ERROR_SENTINEL = -2147483647;  // INT_MIN + 1

// Lowered form of:
//   int may_throw(int x) {
//     if (x < 0) throw -1;
//     return x * 2;
//   }
int may_throw_lowered(int x) {
    if (x < 0) {
        __exc_state.flag    = 1;
        __exc_state.type_id = 1;
        __exc_state.value   = -1;
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

    if (__exc_state.flag) {
        int       caught_type = __exc_state.type_id;
        long long caught_val  = __exc_state.value;

        // __cxa_begin_catch -> clear flag
        __exc_state.flag = 0;

        if (caught_type == 1) {
            return (int)caught_val;
        }

        // No match -> resume (re-raise)
        __exc_state.flag = 1;
        return ERROR_SENTINEL;
    }

    return result;
}

// Accessors used by SAW specs.
_Bool get_error_flag(void)   { return __exc_state.flag; }
int   get_error_value(void)  { return (int)__exc_state.value; }
void  reset_error_state(void) {
    __exc_state.flag    = 0;
    __exc_state.type_id = 0;
    __exc_state.value   = 0;
}
