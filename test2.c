#include <stdlib.h>

extern size_t __breakpoint__zero_inc(size_t*);

size_t zero_inc(size_t x) {
  if (x == 0) {
    __breakpoint__zero_inc(&x);
    ++x;
  }
  return x;
}

