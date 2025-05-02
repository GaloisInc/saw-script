#include <stdlib.h>
#include <stdint.h>

/* Add two numbers using a while loop that repeatedly increments */
int64_t add_loop (int64_t x, int64_t y) {
  uint64_t ret = x;
  for (uint64_t i = y; i > 0; -- i) {
    ret++;
  }
  return ret;
}

/* Returns the sign of the sum of the two inputs, using add_loop! */
int64_t sign_of_sum (int64_t x, int64_t y) {
  int64_t d = add_loop(x, y);
  if (d > 0) {
    return 1;
  } else if (d < 0) {
    return -1;
  } else {
    return 0;
  }
}

/* Returns 1 if x < y+z, -1 if x > y+z, and 0 otherwise, using add_loop
   for the sum and sign_of_sum for the comparison! */
int64_t compare_sum (int64_t x, int64_t y, int64_t z) {
  return sign_of_sum(-x, add_loop(y, z));
}