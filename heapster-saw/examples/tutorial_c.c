#include <stdint.h>

// Simple function that adds it's two inputs.
uint64_t add (uint64_t x, uint64_t y) { return x + y; }

// A copy of `add`, that we will use to miss-type a function
uint64_t add_mistyped (uint64_t x, uint64_t y) { return x + y; }

// Simple function that increments the value in a pointer
void incr_ptr (uint64_t *x) { *x += 1; }

// Struct that represents the three coordinates for a 3D vector
typedef struct { uint64_t x; uint64_t y; uint64_t z; } vector3d;

// function that computes the norm of a 3D vector
// || (x,y,z) || = x^2+y^2+z^2
uint64_t norm_vector (vector3d *v) { return (v->x * v->x + v->y * v->y + v->z * v->z); }
