#include <stdbool.h>
#include <stdint.h>

struct s {
  int32_t w;
  uint8_t x1:1;
  uint8_t x2:2;
  uint8_t y:1;
  int32_t z;
};

void set_y(struct s *ss, bool y) {
  ss->y = y;
}
