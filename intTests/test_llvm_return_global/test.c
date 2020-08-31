#include <stdint.h>
#include <stdlib.h>

uint64_t glob;

uint64_t *foo () {
	return &glob;
}

int bar () {
	return (foo() == &glob);
}
