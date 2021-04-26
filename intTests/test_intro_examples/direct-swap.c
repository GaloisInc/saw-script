#include <stdlib.h>
#include <stdint.h>

void swap_direct(uint32_t *x, uint32_t *y) {
    uint32_t tmp;
    tmp = *x;
    *x = *y;
    *y = tmp;
}
