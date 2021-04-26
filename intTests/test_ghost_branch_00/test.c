extern unsigned x;

unsigned f(unsigned i) {
  if (i < 42) {
    x = i;
    return x;
  }
  x = 2 * i;
  return x;
}

unsigned g(unsigned i) {
  return f(i);
}
