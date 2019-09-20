extern int x;

int get() {
  return x;
}

void f(int i) {
  x = i;
}

void g(int i) {
  x = i;
}

int h(int i) {
  if (i < 42) {
    f(i);
  } else {
    g(i);
  }
  return get();
}
