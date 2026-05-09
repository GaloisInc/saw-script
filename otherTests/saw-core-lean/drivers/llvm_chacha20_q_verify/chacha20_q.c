/*
** ChaCha20 quarterround function. Public wrapper exposing the
** static `qround` from examples/chacha20/chacha20.c, but
** restructured to take 4 separate pointers (a, b, c, d) instead
** of an array+indices interface — matches the per-pointer pattern
** the Salsa20 quarterround verify uses (case study C, #144), so
** the SAW driver mirrors that case study's setup.
**
** The 4-step add/xor/rotate cycle is per RFC 7539.
*/

static unsigned int
l32(unsigned int x, unsigned int n)
{
  return (x << n) | (x >> (-n & 31));
}

void
chacha20_qround(unsigned int* a,
                unsigned int* b,
                unsigned int* c,
                unsigned int* d)
{
  *a = *a + *b; *d = l32(*d ^ *a, 16);
  *c = *c + *d; *b = l32(*b ^ *c, 12);
  *a = *a + *b; *d = l32(*d ^ *a,  8);
  *c = *c + *d; *b = l32(*b ^ *c,  7);
}
