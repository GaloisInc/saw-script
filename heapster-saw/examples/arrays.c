#include <stdlib.h>
#include <stdint.h>

/* Test if an array contains 0 recursively */
int64_t contains0_rec (int64_t *arr, int64_t len, int64_t i) {
  if (i >= len) {
    return 0;
  } else if (arr[i] == 0) {
    return 1;
  } else {
    return contains0_rec (arr, len, i+1);
  }
}

/* Like contains0_rec but with len first */
int64_t contains0_rec_ (uint64_t len, int64_t *arr, uint64_t i) {
  if (i >= len) {
    return 0;
  } else if (arr[i] == 0) {
    return 1;
  } else {
    return contains0_rec_ (len, arr, i+1);
  }
}

/* Test if an array contains 0 */
int64_t contains0 (int64_t *arr, uint64_t len) {
  for (uint64_t i = 0; i < len; ++i) {
    if (arr[i] == 0) { return 1; }
  }
  return 0;
}

/* Test if an array contains 0 */
int64_t contains0_after (int64_t *arr, uint64_t len, uint64_t i) {
  for (; i < len; ++i) {
    if (arr[i] == 0) { return 1; }
  }
  return 0;
}

/* Test if a sorted array contains 0 by divide-and-conquer */
int64_t contains0_sorted_rec (int64_t *arr, uint64_t len) {
  if (len == 0) {
    return 0;
  } else if (len == 1) {
    return arr[0] == 0 ? 1 : 0;
  } else {
    uint64_t halfway = len / 2;
    if (arr[halfway] > 0) {
      return contains0_sorted_rec (arr, halfway);
    } else {
      return contains0_sorted_rec (arr+halfway, len - halfway);
    }
  }
}

/* Zero out an array */
void zero_array (int64_t *arr, uint64_t len) {
  for (uint64_t i = 0; i < len; ++i) {
    arr[i] = 0;
  }
}

/* Zero out an array starting at a given offset */
void zero_array_from (int64_t *arr, uint64_t len, uint64_t off) {
  for (; off < len; ++off) {
    arr[off] = 0;
  }
}

/* Zeroes every negative element of an array and returns the
   sum of the results */
uint64_t filter_and_sum_pos (int64_t * arr, uint64_t len) {
  uint64_t sum = 0;
  for (uint64_t i = 0; i < len; ++i) {
    if (arr[i] < 0) {
      arr[i] = 0;
    }
    sum += arr[i];
  }
  return sum;
}

uint64_t sum_2d (int64_t **arr, uint64_t l1, uint64_t l2) {
  uint64_t sum = 0;
  for (uint64_t i = 0; i < l1; ++i) {
    for (uint64_t j = 0; j < l2; ++j) {
      sum += arr[i][j];
    }
  }
  return sum;
}

/* Finds the sum of the elements of an array by incrementing the given pointer
   instead of using a for loop over an index */
uint64_t sum_inc_ptr(const uint8_t *arr, size_t len) {
  uint64_t sum = 0;
  while (len--) {
    sum += arr[0];
    arr += 1;
  }
  return sum;
}

/* Like the above, but uses an array of int64_t */
uint64_t sum_inc_ptr_64(const uint64_t *arr, size_t len) {
  uint64_t sum = 0;
  while (len--) {
    sum += arr[0];
    arr += 8;
  }
  return sum;
}

/* For an array of even length, returns the sum of the even components of the
   array minus the sum of the odd components of an array */
uint64_t even_odd_sums_diff(const uint64_t *arr, size_t len) {
  uint64_t sum = 0;
  for (uint64_t i = 1; i < len; i += 2) {
    sum += arr[i-1] - arr[i];
  }
  return sum;
}

uint64_t alloc_sum_array_test (void) {
  uint64_t X[8];
  X[0] = 0; X[1] = 1; X[2] = 2; X[3] = 3;
  X[4] = 4; X[5] = 5; X[6] = 6; X[7] = 7;
  /*
  for (uint64_t i = 0; i < 16; ++i) {
    X[i] = i;
  }
  */
  return sum_inc_ptr_64 (X, 8);
}

/* A dummy function used as a hint for Heapster that arr is initialized up
   through index i */
void array_init_hint (uint64_t len, uint64_t i, uint64_t *arr) { return; }

/* Test out an initialization loop for a locally-allocated array, using a
   function that initializes an array X to X[i]=i for each i and then sums the
   resulting array by calling sum_inc_ptr_64. This is similar to
   alloc_sum_array_test, except that it initializes the array in a loop. */
uint64_t array_init_loop_test (void) {
  uint64_t X[8];
  uint64_t i = 0;

  array_init_hint (8, i, X);
  for (; i < 8; ++i) {
    X[i] = i;
  }
  return sum_inc_ptr_64 (X, 8);
}
