#include <stdbool.h>
#include <stdint.h>

struct s {
  int32_t w;
  uint8_t x1:1;
  uint8_t x2:2;
  uint8_t y:1;
  int32_t z;
};

uint8_t get_x2(struct s *ss) {
  return ss->x2;
}

bool get_y(struct s *ss) {
  return ss->y;
}

void set_x2(struct s *ss, uint8_t x2) {
  ss->x2 = x2;
}

void set_y(struct s *ss, bool y) {
  ss->y = y;
}

void set_x2_alt(struct s *ss, uint8_t x2) {
  set_x2(ss, x2);
}

void set_y_alt(struct s *ss, bool y) {
  set_y(ss, y);
}
