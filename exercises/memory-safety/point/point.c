#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct point {
    uint32_t x;
    uint32_t y;
} point;

point ZERO = {0, 0};

bool point_eq(const point *p1, const point *p2) {
    return p1->x == p2->x && p1->y == p2-> y;
}

point* point_new(uint32_t x, uint32_t y) {
    point* ret = malloc(sizeof(point));
    ret->x = x;
    ret->y = y;
    return ret;
}

point* point_copy(const point* p) {
    return point_new(p->x, p->y);
}

point* point_add(const point *p1, const point *p2) {
    // Save an addition by checking for zero
    if (point_eq(p1, &ZERO)) {
        return point_copy(p2);
    } 
    
    if (point_eq(p2, &ZERO)) {
        return point_copy(p1);
    }

    return point_new(p1->x + p2->x, p1->y + p2->y);
}