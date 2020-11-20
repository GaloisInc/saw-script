#include <stdint.h>

uint64_t g1(uint64_t x) {
  int i = 0;
  uint64_t r = x;
  do {
    r = r+1;
  } while ( i++ < 3 && r == 0 );
  return r;
}

// NB the termination of the following loop
// is a bit tricky because of the interaction
// between short-cutting '&&' and the 'i++'
// expression.
uint64_t g2(uint64_t x) {
  int i = 0;
  uint64_t r = x;
  do {
    r = r+1;
  } while ( r == 0 && i++ < 3 );
  return r;
}
