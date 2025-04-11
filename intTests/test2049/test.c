#include <stdint.h>

static uint8_t table[256];

void assign(uint8_t k, uint8_t v) {
   table[k] = v;
}

void zero(uint8_t k) {
  assign(k, 0);
}

