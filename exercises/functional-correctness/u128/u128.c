#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <strings.h>

void increment_u128(uint64_t x[2]) {
    if (++x[1] == 0) {
        ++x[0];
    }
}

bool eq_u128(uint64_t x[2], uint64_t y[2]) {
    return !bcmp(x, y, 16);
}