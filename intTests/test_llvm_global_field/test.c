#include <stdint.h>

typedef struct {
	uint32_t first;
	uint32_t second;
} pair_t;

pair_t the_pair;

void set (uint32_t x, uint32_t y) {
	the_pair.first = x;
	the_pair.second = y;
}
