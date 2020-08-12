#include <stdint.h>

typedef struct {
    uint32_t x;
    uint8_t y;
} foo;

typedef struct {
    uint8_t a;
    foo b[10];
} bar;

void dummy (foo *x, bar *y) {
    return;
}
