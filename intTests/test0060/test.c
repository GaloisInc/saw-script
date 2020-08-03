#include <inttypes.h>

uint32_t *id_p(uint32_t *p) {
    return p;
}

uint32_t *incr_p(uint32_t *p) {
    return p + 1;
}

void add_two(uint32_t *p) {
    p = (uint64_t *)p;
    *p = *p + 2;
}
