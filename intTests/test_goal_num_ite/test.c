#include<stdint.h>

void g(uint64_t* a) {
  *a = 2*(*a);
};

void h(uint64_t* a) {
  *a = 3*(*a);
};

void f(uint64_t* x) {
  g(x);
  h(x);
};
