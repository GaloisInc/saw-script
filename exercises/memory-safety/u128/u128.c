#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <strings.h>

// Increment a 128-bit uint (represented as an array of 2 64-bit uints)
void increment_u128(uint64_t x[2]) {
    if (++x[0] == 0) {
        ++x[1];
    }
}

bool eq_u128(const uint64_t x[2], const uint64_t y[2]) {
    // "The bcmp() function compares the two byte sequences s1 and s2 of length
    // n each. If they are equal, and in particular if n is zero, bcmp() returns
    // 0. Otherwise it returns a nonzero result." --bcmp man page
    // The type signature for bcmp is:
    //     int bcmp(const void *b1, const void *b2, size_t len);
    return !bcmp(x, y, 16);
}