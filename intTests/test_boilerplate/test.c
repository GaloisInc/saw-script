#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

const uint64_t GLOBAL = 1;

uint64_t test0(uint64_t x, uint64_t y) {
	return x + y;
}

uint64_t test1() {
	return test0(GLOBAL, GLOBAL);
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
