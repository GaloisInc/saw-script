#include <stdlib.h>
#include <stdint.h>

typedef struct padded_struct {
  uint64_t padded1;
  uint8_t padded2;
  uint64_t padded3;
  uint8_t padded4;
} padded_struct;

padded_struct *alloc_padded_struct (void) {
  padded_struct *ret = malloc (sizeof(padded_struct));
  ret->padded1 = 0;
  ret->padded2 = 0;
  ret->padded3 = 0;
  ret->padded4 = 0;
  return ret;
}

void padded_struct_incr_all (padded_struct *p) {
  p->padded1++;
  p->padded2++;
  p->padded3++;
  p->padded4++;
}
