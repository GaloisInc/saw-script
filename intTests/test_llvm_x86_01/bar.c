#include <stdint.h>
#include <stdio.h>

extern void foo(uint64_t *i, uint64_t j);

void bar() {
	uint64_t i = 42;
	foo(&i, 1337);
	puts("bar");
	printf("%lu\n", i);
};
