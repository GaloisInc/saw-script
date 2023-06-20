#include<stdint.h>
#include<stdlib.h>

uint8_t foo(const uint8_t *a, size_t n) {
  uint8_t s = 0;
  size_t i = 0;
  do {
    s += a[i];
    ++i;
  } while (i < n);
  return s;
}

uint64_t bar(const uint64_t *a, size_t n) {
  uint64_t s = 0;
  size_t i = 0;
  do {
    s += a[i];
    ++i;
  } while (i < n);
  return s;
}

