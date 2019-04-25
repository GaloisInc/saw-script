#include <stdlib.h>

extern size_t __breakpoint__inv(size_t*);

size_t zero_inc(size_t x) {
  if (x == 0) {
    __breakpoint__inv(&x);
    ++x;
  }
  return x;
}

