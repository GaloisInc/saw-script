#include <stdlib.h>

extern size_t __cutpoint__inv(size_t*);

size_t add2(size_t x) {
  ++x;
  __cutpoint__inv(&x);
  ++x;
  return x;
}

