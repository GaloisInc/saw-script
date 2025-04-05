#include <stdlib.h>
#include <stdint.h>

typedef struct list64_t {
  int64_t data;
  struct list64_t *next;
} list64_t;

/* Test if a value is the head of a list, returning 1 if so and 0 otherwiese */
int64_t is_head (int64_t x, list64_t *l) {
  if (l == NULL) {
    return 0;
  } else if (l->data == x) {
    return 1;
  } else {
    return 0;
  }
}

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

/* Test if some element of a list satisfies a given predicate */
int64_t any (int64_t (*pred) (int64_t), list64_t *l) {
  if (l == NULL) {
    return 0;
  } else if (pred (l->data)) {
    return 1;
  } else {
    return any (pred, l->next);
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

/* Insert a value into a sorted list */
list64_t *sorted_insert (int64_t x, list64_t *l) {
  if (l == NULL) {
    list64_t *ret = malloc (sizeof (struct list64_t));
    ret->data = x;
    ret->next = NULL;
    return ret;
  } else if (x <= l->data) {
    list64_t *ret = malloc (sizeof (struct list64_t));
    ret->data = x;
    ret->next = l;
    return ret;
  } else {
    l -> next = sorted_insert (x, l->next);
    return l;
  }
}
/* Insert an already-allocated list element into a sorted list */
list64_t *sorted_insert_no_malloc (list64_t *x, list64_t *l) {
  if (l == NULL) {
    x -> next = NULL;
    return x;
  } else if (x -> data <= l->data) {
    x -> next = l;
    return x;
  } else {
    l -> next = sorted_insert_no_malloc (x, l->next);
    return l;
  }
}
