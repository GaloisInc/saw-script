#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t rotatel(uint32_t x, uint32_t a) {
  return (x << a | x >> (32 - a));
}
