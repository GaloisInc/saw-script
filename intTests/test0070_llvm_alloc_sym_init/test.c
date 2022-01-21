#include <stdlib.h>

int f(int *x)
{
  return *x;
}

int test_f_calloc()
{
  int *x = (int *) calloc(1, sizeof(int));
  return f(x);
}

int test_f_malloc()
{
  int *x = (int *) malloc(sizeof(int));
  return f(x);
}

