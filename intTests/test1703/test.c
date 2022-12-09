#include <stdint.h>

uint32_t weird(uint32_t cv[8], uint8_t i) {
    return cv[i % 8];
}
