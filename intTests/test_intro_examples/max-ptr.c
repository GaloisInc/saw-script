void max_ptr(int *p, int *q) {
  if (*p > *q) {
    int tmp = *p;
    *p = *q;
    *q = tmp;
  } else {
    return;
  }
}
