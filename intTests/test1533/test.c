#include <stdint.h>

struct s {
  uint8_t x1;
  uint8_t x2;
};

uint8_t get_x2(struct s *ss) {
  return ss->x2;
}

int main() {
  return 0;
}
