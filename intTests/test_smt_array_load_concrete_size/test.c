#include <stdint.h>
#include <string.h>

int mix(uint8_t block[128], uint32_t n, uint8_t *data, size_t len) {
  size_t left = 128 - n;

  if (len < left) {
    memcpy(block + n, data, len);
  } else {
    memcpy(block + n, data, left);
  }
  return 1;
}
