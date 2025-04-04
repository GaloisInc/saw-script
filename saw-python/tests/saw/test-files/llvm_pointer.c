#include <stdint.h>
#include <stdlib.h>

void f(uint8_t **x) {
  *x = malloc(sizeof(uint8_t));
  **x = 42;
}
