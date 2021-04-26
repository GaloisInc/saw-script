#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct uint128_t {
  union {
    uint8_t bytes[16];
    uint32_t dw[4];
    uint64_t qw[2];
  } u;
};

uint32_t get_lo(const uint64_t x)
{
  return (uint32_t) x;
}

uint32_t get_hi(const uint64_t x)
{
  return (uint32_t) (x >> 32);
}

void add(struct uint128_t *r, const struct uint128_t *a, const struct uint128_t *b)
{ 
  uint32_t c = 0;
  for (int i = 0; i < 4; ++i)
  {
    uint64_t acc = ((uint64_t) a->u.dw[i]) + ((uint64_t) b->u.dw[i]) + ((uint64_t) c);
    r->u.dw[i] = get_lo(acc);
    c = get_hi(acc);
  }
}

void sum(struct uint128_t *s, const struct uint128_t *a, size_t n)
{
  memset(s, 0, sizeof(*s));
  for (int i = 0; i < n; ++i)
  {
    struct uint128_t tmp = *s;
    add(s, &tmp, &a[i]);
  }
}

