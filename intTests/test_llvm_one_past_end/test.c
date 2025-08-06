#include <stdint.h>

void increment_span(uint32_t *lo, uint32_t *hi) {
    for (uint32_t * cursor = lo; cursor < hi; cursor++) {
        (*cursor)++;
    }
}

void increment(uint32_t *p) {
    (*p)++;
}
