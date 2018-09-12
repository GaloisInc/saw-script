#include <stdlib.h>

typedef struct list {
  int data;
  struct list *next;
} list;

int length (list *l) {
  if (l == NULL) { return 0; }
  else { return 1 + length (l->next); }
}

list *nil () { return NULL; }

list *cons (int x, list *l) {
  list *ret = malloc (sizeof (struct list));
  ret->data = x;
  ret->next = l;
  return ret;
}

list *mk_list_123 () {
  return cons (0, cons (1, cons (2, NULL)));
}
