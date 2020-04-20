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

/* Serach for a specific value in a list */
list64_t *find_elem (int64_t x, list64_t *l) {
  if (l == NULL) {
    return NULL;
  } else if (l->data == x) {
    return l;
  } else {
    return find_elem (x, l->next);
  }
}

/* Insert an already-allocated list element into a sorted list */
list64_t *sorted_insert (list64_t *x, list64_t *l) {
  if (l == NULL) {
    x -> next = NULL;
    return x;
  } else if (x -> data <= l->data) {
    x -> next = l;
    return x;
  } else {
    l -> next = sorted_insert (x, l->next);
    return l;
  }
}
