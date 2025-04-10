int glb;

void foo(const int *x) {}

void bar(const int *x) {
  foo(x);
}

