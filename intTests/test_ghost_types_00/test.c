#include "stdlib.h"

extern unsigned x;
extern unsigned char y;

unsigned f(unsigned i) {
  x = i;
  return x;
}

unsigned char g(unsigned i) {
  y = (unsigned char) (i / 8);
  return y;
}

unsigned h(unsigned i) {
  f(i);
  g(i);
  if (i < 32) {
    return f(i);
  }
  return (unsigned) g(i);
}
