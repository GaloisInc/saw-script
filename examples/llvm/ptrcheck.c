#include <stdint.h>
#include <stdlib.h>

typedef struct {
    uint32_t x;
    uint32_t y;
    uint32_t z;
    uint32_t w;
} s;

uint32_t f(s* sp) {
    if(sp == NULL) {
        return 1;
    } else if(&(sp->x) == NULL) {
        return 2;
    } else if(&(sp->y) == NULL) {
        return 3;
    } else if(&(sp->z) == NULL) {
        return 4;
    } else if(&(sp->w) == NULL) {
        return 5;
    } else {
        return 0;
    }
}
