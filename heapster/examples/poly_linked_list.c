#include <stdlib.h>
#include <stdint.h>

/* A "polymorphic" linked list uses elements that can be cast to pointers or integers */
typedef struct list_t {
  uintptr_t data;
  struct list_t *next;
} list_t;

/* Test if some element of a list satisfies a given predicate */
int64_t any (int64_t (*pred) (uintptr_t), list_t *l) {
  if (l == NULL) {
    return 0;
  } else if (pred (l->data)) {
    return 1;
  } else {
    return any (pred, l->next);
  }
}
