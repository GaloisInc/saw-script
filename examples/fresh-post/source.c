extern int whoknows(void);

int example(void) {
  int y = whoknows();
  return y-y;
}

int bad(void) {
  int x = whoknows();
  int y = whoknows();
  return x-y;
}
