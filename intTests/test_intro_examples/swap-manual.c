#include <assert.h>
#include <stdlib.h>
#include <stdint.h>

#include "swap-correct.c"

int main() {
    assert(swap_correct(0, 0));
    assert(swap_correct(0, 1));
    assert(swap_correct(1, 0));
    assert(swap_correct(32, 76));
    assert(swap_correct(0xFFFFFFFF, 0));
    assert(swap_correct(0, 0xFFFFFFFF));
    assert(swap_correct(0xFFFFFFFF, 0xFFFFFFFF));
    return 0;
}
