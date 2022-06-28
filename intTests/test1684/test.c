#include <stdint.h>

struct a {
  uint16_t x;
  uint32_t y;
};

struct b {
  struct a aa;
};

void f(struct b *bb) {}
