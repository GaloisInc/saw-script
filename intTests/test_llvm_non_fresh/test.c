#include <stdint.h>
#include <stdlib.h>

uint64_t *foo (uint64_t *x) {
	return x;
}

int bar (uint64_t *x) {
	return (foo(x) == x);
}
