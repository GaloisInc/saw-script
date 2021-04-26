#include <stdlib.h>
#include <stdint.h>

void swap_xor(uint32_t *x, uint32_t *y) {
    *x = *x ^ *y;
    *x = *x ^ *y;
    *y = *x ^ *y;
}
