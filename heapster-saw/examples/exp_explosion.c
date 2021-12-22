#include <stdlib.h>
#include <stdint.h>

#define op(x,y) x ^ (y << 1)

int64_t exp_explosion(int64_t x0) {
  int64_t x1 = op(x0, x0);
  int64_t x2 = op(x1, x1);
  int64_t x3 = op(x2, x2);
  int64_t x4 = op(x3, x3);
  int64_t x5 = op(x4, x4);
  int64_t x6 = op(x5, x5);
  int64_t x7 = op(x6, x6);
  int64_t x8 = op(x7, x7);
  int64_t x9 = op(x8, x8);
  int64_t x10 = op(x9, x9);
  int64_t x11 = op(x10, x10);
  int64_t x12 = op(x11, x11);
  int64_t x13 = op(x12, x12);
  int64_t x14 = op(x13, x13);
  int64_t x15 = op(x14, x14);
  return x15;
}
