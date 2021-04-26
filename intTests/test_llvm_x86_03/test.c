#include <stdint.h>
#include <stdio.h>

extern uint64_t foo();

void bar() {
	foo();
};
