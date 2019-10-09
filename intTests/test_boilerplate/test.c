#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

uint64_t GLOBAL = 0;

uint64_t test0(uint64_t x, uint64_t y) {
	return x + y;
}

void test1() {
	GLOBAL += test0(GLOBAL, GLOBAL);
}

uint64_t test2(uint64_t *buf) {
	return buf[5];
}

void entrypoint() {
	test0(1, 2);
	test1();

	uint64_t buf[20];
	memset(buf, 1, sizeof(buf));
	test2(buf);
}
