#include <stdint.h>

uint32_t foo(uint32_t *x) {
	uint32_t tmp = *x + 1;
	*x += 42;
	return tmp;
};

uint32_t bar() {
	uint32_t val = 1;
	return foo(&val) + val;
};
