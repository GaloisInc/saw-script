#include <stdint.h>
#include <stdlib.h>

uint64_t *foo () {
	return NULL;
}

int bar () {
	return (foo() == NULL);
}
