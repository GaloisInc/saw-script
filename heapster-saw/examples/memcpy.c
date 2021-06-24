#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int64_t copy_int (int64_t x) {
  int64_t y;
  memcpy (&y, &x, sizeof (int64_t));
  return y;
}

int64_t copy_ptr_contents (int64_t *x) {
  int64_t y;
  memcpy (&y, x, sizeof (int64_t));
  return y;
}

void copy_ptr (int64_t *x) {
  int64_t *y;
  memcpy (&y, &x, sizeof (int64_t*));
  *y = 5;
}
