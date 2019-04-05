#include <stdlib.h>

extern size_t __breakpoint__inv(size_t*, size_t*, size_t*) __attribute__((noduplicate));

size_t count_n(size_t n) {
  size_t c = 0;
  for (size_t i = 0; __breakpoint__inv(&n, &c, &i), i < n; ++i) {
    ++c;
  }
  return c;
}

