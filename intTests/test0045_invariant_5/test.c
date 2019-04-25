#include <stdint.h>
#include <stdlib.h>

extern void __breakpoint__outer_inv(uint8_t**, size_t*, size_t*, size_t*, size_t*) __attribute__((noduplicate));
extern void __breakpoint__inner_inv(uint8_t**, size_t*, size_t*, size_t*, size_t*) __attribute__((noduplicate));

void multiple_array_inc(uint8_t a[], size_t n, size_t m) {
  size_t i, j;
  for (j = 0; __breakpoint__outer_inv(&a, &n, &m, &i, &j), j < m; ++j) {
    for (i = 0; __breakpoint__inner_inv(&a, &n, &m, &i, &j), i < n; ++i) {
      ++a[i];
    }
  }
}

