#include <stdlib.h>
#include <stdint.h>

#define op(x,y) x ^ (y << 1)

int64_t exp_explosion(int64_t a) {
  int64_t b = op(a, a);
  int64_t c = op(b, b);
  int64_t d = op(c, c);
  int64_t e = op(d, d);
  int64_t f = op(e, e);
  int64_t g = op(f, f);
  int64_t h = op(g, g);
  int64_t i = op(h, h);
  int64_t j = op(i, i);
  int64_t k = op(j, j);
  return op(k, k);
}
