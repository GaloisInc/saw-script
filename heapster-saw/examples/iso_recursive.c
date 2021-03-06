#include <stdlib.h>
#include <stdint.h>

typedef struct list64_t {
  int64_t data;
  struct list64_t *next;
} list64_t;

/* Test if a specific value is in a list, returning 1 if so and 0 otherwise */
int64_t is_elem (int64_t x, list64_t *l) {
  if (l == NULL) {
    return 0;
  } else if (l->data == x) {
    return 1;
  } else {
    return is_elem (x, l->next);
  }
}
