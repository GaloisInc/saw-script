#include <stdint.h>

void write (uint64_t *p, uint64_t x) {
	*p = x;
}

void write_unaligned (uint8_t *p, uint64_t x) {
	write((uint64_t *)(p + 1), x);
}
