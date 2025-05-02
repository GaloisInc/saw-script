#include <stdio.h>

typedef struct BI {
  unsigned int i[2][4];
} BI_t;

void f(BI_t* w) {
  for( int j=0; j<2; j++) {
    for (int k=0; k<4; k++) {
      (w->i)[j][k] = 0;
    }
  }
}

int main() {
  BI_t x;
  x.i[1][3] = 42;
  f(&x);
  printf( "%u\n", x.i[1][3] );
}
