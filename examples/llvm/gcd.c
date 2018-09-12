
int gcd_rec (int a, int b) {
  if (b == 0) {
    return a;
  } else {
    return gcd_rec (b, a % b);
  }
}

int gcd_loop (int a, int b) {
  int temp_b;
  while (b != 0) {
    temp_b = b;
    b = a % b;
    a = temp_b;
  }
  return a;
}
