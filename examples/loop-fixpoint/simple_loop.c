// simple_loop.c — A simple loop for testing fixpoint support with llvm_verify
//
// Compile with: clang -O0 -emit-llvm -c simple_loop.c -o simple_loop.bc

#include <stdint.h>
#include <stddef.h>

// Sum integers from 0 to n-1.
// Closed form: n*(n-1)/2
uint32_t sum_upto(uint32_t n) {
    uint32_t acc = 0;
    for (uint32_t i = 0; i < n; i++) {
        acc += i;
    }
    return acc;
}

// Zero-fill a buffer of `len` bytes.
void zero_fill(uint8_t *buf, size_t len) {
    for (size_t i = 0; i < len; i++) {
        buf[i] = 0;
    }
}

// Count nonzero bytes in a buffer.
uint32_t count_nonzero(const uint8_t *buf, uint32_t len) {
    uint32_t count = 0;
    for (uint32_t i = 0; i < len; i++) {
        if (buf[i] != 0) {
            count++;
        }
    }
    return count;
}
