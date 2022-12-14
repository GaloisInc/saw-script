#include <stdint.h>
#include <stdlib.h>

// Swap two pointers using a temporary variable
void swap(uint32_t *x, uint32_t *y) {
    uint32_t tmp = *x;
    *x = *y;
    *y = tmp;
}

// Swap two pointers using XOR
void xor_swap(uint32_t *x, uint32_t *y) {
    *x ^= *y;
    *y ^= *x;
    *x ^= *y;
}

// selection sort on an array `a` with `len` elements
void selection_sort(uint32_t *a, size_t len) {
    for (size_t i = 0; i < len - 1; ++i) {
        size_t j_min = i;
        for (size_t j = i; j < len; ++j) {
            if (a[j] < a[j_min]) {
                j_min = j;
            }
        }
        swap(a+i, a+j_min);
    }
}