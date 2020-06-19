#include <stdlib.h>

int glob;

int foo (int *x) {
	return (x == &glob);
}

int bar () {
	return foo(&glob);
}
