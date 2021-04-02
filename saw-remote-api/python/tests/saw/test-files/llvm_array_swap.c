#include <stdint.h>

void array_swap(uint32_t a[2]) {
    uint32_t tmp = a[0];
    a[0] = a[1];
    a[1] = tmp;
}
