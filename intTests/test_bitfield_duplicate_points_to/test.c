#include <stdbool.h>
#include <stdint.h>

struct s {
  int32_t w;
  uint8_t x1:1;
  uint8_t x2:2;
  uint8_t y:1;
  int32_t z;
};

bool get_y(struct s *ss) {
  return ss->y;
}
