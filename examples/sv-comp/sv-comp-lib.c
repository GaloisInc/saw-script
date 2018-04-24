#include <stdio.h>
#include <stdlib.h>

void __VERIFIER_assume(int p) {
}

void __VERIFIER_error() {
    printf("Reached __VERIFIER_error()!\n");
    exit(EXIT_FAILURE);
}

unsigned int __VERIFIER_nondet_uint(void) {
  static int idx = 0;
  return uints[idx++];
}
