#include "stdint.h"
#include "stdbool.h"

void foo(uint8_t xs[4]);

void bar() {
    uint8_t xs[4] = {0,1,2,3};
    for (int i = 0; i < 10; ++i) {
        foo(xs);
    }
}
