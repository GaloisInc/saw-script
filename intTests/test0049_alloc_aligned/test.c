#include <stdint.h>

typedef __attribute__((aligned(64))) struct syndrome_s
{
  uint64_t qw[8];
} syndrome_t;

uint64_t dup(syndrome_t *s)
{
  return s->qw[0];
}

