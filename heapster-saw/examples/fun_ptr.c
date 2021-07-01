
int bar (int x) {
  return x+1;
}

int foo (int (*f)(int)) {
  return f (1);
}

int call_foo () {
  return foo (&bar);
}
