#include <stdlib.h>
#include <stdint.h>

void xor_swap(uint32_t *x, uint32_t *y) {
    *x = *x ^ *y;
    *y = *x ^ *y;
    *x = *x ^ *y;
}
