#include <stdlib.h>
#include <stdint.h>

uint32_t add(uint32_t x, uint32_t y) {
    return x + y;
}

uint32_t add2(uint32_t x, uint32_t y) {
    return (y + 1 + x) - 1;
}
