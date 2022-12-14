#include <stdint.h>
#include <stdlib.h>

void swap(uint32_t *x, uint32_t *y) {
    uint32_t tmp = *x;
    *x = *y;
    *y = tmp;
}

void xor_swap(uint32_t *x, uint32_t *y) {
    *x ^= *y;
    *y ^= *x;
    *x ^= *y;
}

// selection sort
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

size_t argmin(const uint32_t *a, size_t len) {
    size_t j_min = 0;
    for (size_t j = 0; j < len; ++j) {
        if (a[j] < a[j_min]) {
            j_min = j;
        }
    }
    return j_min;
}

void swap_array(uint32_t *a, size_t i, size_t j) {
    swap(a+i, a+j);
}

void selection_sort_composed(uint32_t *a, size_t len) {
    for (size_t i = 0; i < len - 1; ++i) {
        size_t j_min = i + argmin(a+i, len-i);
        swap_array(a, i, j_min);
    }
}

void wacky_sort(uint32_t *a, size_t len) {
    for (size_t i = 0; i < 4; ++i) {
        size_t swap_idx = (argmin(a, len) + i) % len;
        swap_array(a, 0, swap_idx);
        swap_array(a, 0, swap_idx);
    }
    selection_sort_composed(a, len);
}