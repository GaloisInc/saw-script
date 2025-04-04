#include<stdint.h>

void swap(uint32_t *a, uint32_t *b) {
    uint32_t tmp = *a;
    *a = *b;
    *b = tmp;
}

void xor_swap(uint32_t *a, uint32_t *b) {
    *a ^= *b;
    *b ^= *a;
    *a ^= *b;
}
