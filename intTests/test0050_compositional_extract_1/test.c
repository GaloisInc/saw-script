unsigned foo(unsigned *p, unsigned x)
{
  *p += x;
  return *p;
}

void bar(unsigned *p)
{
  foo(p, foo(p, 1));
}

