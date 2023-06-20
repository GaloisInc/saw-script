#include<stdint.h>
#include<stdlib.h>

void foo(uint8_t *a, size_t n, uint8_t c) {
  size_t i = 0;
  do {
    a[i] += c;
    ++i;
  } while (i < n);
}

void bar(uint64_t *a, size_t n, uint64_t c) {
  size_t i = 0;
  do {
    a[i] += c;
    ++i;
  } while (i < n);
}

