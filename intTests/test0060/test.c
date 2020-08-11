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

void array_swap(uint32_t a[2]) {
    uint32_t tmp = a[0];
    a[0] = a[1];
    a[1] = tmp;
}

/* packed attribute to get LLVM to not pad the struct */
typedef struct __attribute__((packed)) {
    uint32_t x;
    uint32_t y;
} foo;

void struct_swap(foo *f) {
    uint32_t tmp = f->x;
    f->x = f->y;
    f->y = tmp;
}
