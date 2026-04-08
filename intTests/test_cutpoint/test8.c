#include <stdlib.h>

extern size_t __cutpoint__inv(size_t *) __attribute__((noduplicate));

size_t count_forever(void) {
  size_t c = 0;
  while (__cutpoint__inv(&c), 1) {
    ++c;
  }
  return 71;
}

