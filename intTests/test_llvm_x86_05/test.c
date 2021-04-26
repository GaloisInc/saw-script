#include <stdint.h>
#include <stdio.h>

extern uint32_t returntest();

uint32_t test() {
	return returntest();
};
