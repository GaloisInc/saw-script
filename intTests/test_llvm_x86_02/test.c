#include <stdint.h>
#include <stdio.h>

extern void increment(uint64_t *i);

void test() {
	uint64_t i = 42;
	increment(&i);
};
