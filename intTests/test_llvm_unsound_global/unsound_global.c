// unsound_global.c

#include <stdint.h>
#include <stdio.h>

uint32_t TEST;

uint32_t GLOBAL[2];

uint32_t foo(uint32_t x) {
	GLOBAL[1] = x;
	return x + 1;
};

uint32_t bar() {
	TEST = 42;
	GLOBAL[1] = 0;
	uint32_t val = foo(1);
	printf("%u\n", TEST);
	// GLOBAL[1] = 0;
	return val + GLOBAL[1];
};
