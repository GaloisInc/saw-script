#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void foo(uint8_t *dest, uint8_t *src, size_t size)
{
  memcpy(dest, src, size);
}

void bar(uint64_t *a, uint64_t *b, size_t len)
{
  foo((uint8_t*) a, (uint8_t*) b, len * sizeof(uint64_t));
}

