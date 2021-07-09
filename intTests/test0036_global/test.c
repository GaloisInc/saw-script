unsigned int x = 0;

unsigned int f(unsigned int y) {
  x = x + 1;
  return x + y;
}

unsigned int g(unsigned int z) {
  x = x + 2;
  return x + z;
}

unsigned int h(unsigned int w) {
  return g(f(w));
}
