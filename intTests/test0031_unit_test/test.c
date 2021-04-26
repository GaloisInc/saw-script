#include <stdio.h>
#include <stdint.h>

typedef struct {
  uint32_t x;
} a_t;

uint32_t foo( a_t* s ) {
  return s->x = 3;
}

uint32_t bar() {
  a_t s[] = { { 1 }, {2}, {3}, {4} };

  return foo( s );
}

int main() {
  printf("%d\n", bar() );
  return 0;
}
