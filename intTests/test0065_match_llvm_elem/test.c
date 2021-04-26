struct s { int x; int y; };

void f(int* x, int* y);
void g(int* x);
void h(int* y, struct s* sp);

void test_f()
{
  int a[2];
  f(a + 1, a);
}

void test_g()
{
  int a[2];
  g(a + 1);
}

void test_h()
{
  struct s s0;
  h(&s0.y, &s0);
}

