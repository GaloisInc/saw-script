#include <stdlib.h>
#include <string.h>

typedef struct A {
  int x;
} A_t;

typedef struct B {
  int y;
} B_t;

typedef struct C {
  A_t a;
  int z;
} C_t;

B_t *cast_as_b(A_t *both) {
  void *v = (void *)both;
  C_t *c = (C_t *)v; // cast to a C so we can get the address of the B
  return (B_t *)(void *)(&c->z);
}

void set(A_t *both) {
  both->x = 10;
  B_t *b = cast_as_b(both);
  b->y = 42;
}

int main() {
  size_t size_of_both = sizeof(A_t) + sizeof(B_t);
  A_t *both = malloc(size_of_both);
  memset(both, 0, size_of_both);
  set(both);
  B_t *b = cast_as_b(both);
  return b->y; // echo $? gives 42
}
