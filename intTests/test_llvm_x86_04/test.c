#include <stdint.h>
#include <stdio.h>

extern uint64_t var;

extern void addvar(uint64_t *i);

void test() {
	(void) var;
	uint64_t i = 42;
	addvar(&i);
};
