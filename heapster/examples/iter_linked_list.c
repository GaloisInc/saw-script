#include <stdlib.h>
#include <stdint.h>

typedef struct list64_t {
  int64_t data;
  struct list64_t *next;
} list64_t;

/* Test if a specific value is in a list, returning 1 if so and 0 otherwise */
int64_t is_elem (int64_t x, list64_t *l) {
  for (; l != NULL; l = l->next) {
    if (l->data == x)
      return 1;
  }
  return 0;
}

/* Compute the length of a list */
int64_t length (list64_t *l) {
  int64_t len = 0;
  for (; l != NULL; l = l->next) {
    ++len;
  }
  return len;
}

/* Increment every element of a linked list */
void incr_list (list64_t *l) {
  for (; l != NULL; l = l->next)
    l->data++;
}
