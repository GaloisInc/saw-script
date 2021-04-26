void f(int* x, int y)
{
  *x = y;
}

void g(int* x, int y)
{
  f(x, y);
}

