#include <stdlib.h>

extern size_t __cutpoint__inv(size_t*);

size_t zero_inc(size_t x) {
  if (x == 0) {
    __cutpoint__inv(&x);
    ++x;
  }
  return x;
}

