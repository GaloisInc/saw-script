#include <stdint.h>
#include <stdlib.h>

const size_t LEN = 42;

void zip_with_add(uint64_t c[LEN], const uint64_t a[LEN], const uint64_t b[LEN]) {
  for (size_t i = 0; i < LEN; i++) {
    c[i] = a[i] + b[i];
  }
}
