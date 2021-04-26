#include "xor-swap.c"

#include "direct-swap.c"

int swap_correct(uint32_t x, uint32_t y) {
    uint32_t x1 = x, x2 = x, y1 = y, y2 = y;
    swap_xor(&x1, &y1);
    swap_direct(&x2, &y2);
    return (x1 == x2 && y1 == y2);
}
