#include <stdlib.h>

typedef struct B {
  int x;
} B_t;

typedef struct A {
  B_t b;
} A_t;

A_t* make_A(B_t b) {
  A_t* ptr = malloc(sizeof(A_t));
  ptr->b = b;
  return ptr;
}
