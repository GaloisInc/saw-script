#include <stdint.h>
#include <stdlib.h>

extern void __breakpoint__array_inc(uint8_t**, size_t*, size_t*) __attribute__((noduplicate));

size_t array_inc(uint8_t a[], size_t n) {
  for (size_t i = 0; __breakpoint__array_inc(&a, &n, &i), i < n; ++i) {
    ++a[i];
  }
  return n;
}

