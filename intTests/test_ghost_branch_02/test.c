extern unsigned x;

unsigned f(unsigned i) {
  if (i < 42) {
    return i;
  }
  x = i;
  return i;
}

unsigned g(unsigned i) {
  return f(i);
}
