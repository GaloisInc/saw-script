#include <stdint.h>
#include <stdlib.h>

extern void __breakpoint__inv(uint8_t**, size_t*, size_t*) __attribute__((noduplicate));

void array_inc(uint8_t a[], size_t n) {
  for (size_t i = 0; __breakpoint__inv(&a, &n, &i), i < n; ++i) {
    ++a[i];
  }
}

