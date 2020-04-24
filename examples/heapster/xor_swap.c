#include <stdlib.h>
#include <stdint.h>

void xor_swap(uint64_t *x, uint64_t *y) {
    *x = *x ^ *y;
    *y = *x ^ *y;
    *x = *x ^ *y;
}
