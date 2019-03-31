#include <stdlib.h>

extern size_t __breakpoint__add2(size_t*);

size_t add2(size_t x) {
  ++x;
  __breakpoint__add2(&x);
  ++x;
  return x;
}

