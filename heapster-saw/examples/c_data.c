#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

/* Increment the first byte pointed to by a 64-bit word pointer */
void incr_u64_ptr_byte (uint64_t *x) {
  uint8_t *x_byte = (uint8_t*)x;
  (*x_byte)++;
}

typedef struct padded_struct {
  uint64_t padded1;
  uint8_t padded2;
  uint64_t padded3;
  uint8_t padded4;
} padded_struct;

/* Allocated a padded_struct */
padded_struct *alloc_padded_struct (void) {
  padded_struct *ret = malloc (sizeof(padded_struct));
  ret->padded1 = 0;
  ret->padded2 = 0;
  ret->padded3 = 0;
  ret->padded4 = 0;
  return ret;
}

/* Increment all fields of a padded_struct */
void padded_struct_incr_all (padded_struct *p) {
  p->padded1++;
  p->padded2++;
  p->padded3++;
  p->padded4++;
}

/* Test endianness by reading the first byte of a word */
int64_t is_little_endian () {
  int64_t x = 1;
  int8_t is_le = *(int8_t*)(&x);
  return is_le;
}

int main (int argc, char **argv) {
  printf ("Little endian test: %lli\n", is_little_endian());
}
