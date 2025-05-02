#include <stdlib.h>
#include <stdint.h>

uint64_t is_null(void *x) {
  if (x == NULL) { return 1; } else { return 0; }
}
