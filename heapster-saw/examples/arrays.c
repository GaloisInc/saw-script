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
