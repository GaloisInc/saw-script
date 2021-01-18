#include <stdint.h>

struct triple {
    uint8_t first[4];
    uint16_t second;
    uint16_t third;
};

void swap (struct triple *p) {
    uint8_t temp1;
    uint16_t temp2;
    temp1 = p->first[0];
    p->first[0] = p->first[3];
    p->first[3] = temp1;
    temp1 = p->first[1];
    p->first[1] = p->first[2];
    p->first[2] = temp1;
    temp2 = p->second;
    p->second = p->third;
    p->third = temp2;
}
