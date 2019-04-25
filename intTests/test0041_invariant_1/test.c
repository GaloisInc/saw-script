#include <stdlib.h>

extern size_t __breakpoint__inv(size_t*);

size_t add2(size_t x) {
  ++x;
  __breakpoint__inv(&x);
  ++x;
  return x;
}

