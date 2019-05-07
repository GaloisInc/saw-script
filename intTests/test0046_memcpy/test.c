#include <stdint.h>
#include <string.h>

void f(uint8_t *x) {
  uint8_t y[8];
  memcpy(x, y, 0);
};

void g(uint8_t *x) {
  uint8_t y[8];
  memcpy(x, y, 1);
};

void h(uint8_t *x) {
  uint8_t y[8];
  x[0] = y[0];
};

