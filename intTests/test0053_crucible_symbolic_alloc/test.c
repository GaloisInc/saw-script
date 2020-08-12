#include <stdlib.h>

void foo(int *x, size_t n, size_t i)
{
  x[i] = 0;
}

void bar(char *x, size_t n, size_t i)
{
  if (i < n)
  {
    foo((int*) x, n / sizeof(int), i / sizeof(int));
  }
}

