#include <stdint.h>

typedef enum { INC_1 , INC_2 } alg;

typedef struct {
  uint32_t x;
} inc_1_st;

typedef struct {
  uint32_t x;
  uint32_t y;
} inc_2_st;

typedef struct {
  alg alg;
  union {
    inc_1_st inc_1_st;
    inc_2_st inc_2_st;
  } inc_st;
} st;

uint32_t inc(st *st) {
  switch (st->alg) {
  case INC_1:
    st->inc_st.inc_1_st.x += 1;
    break;
  case INC_2:
    st->inc_st.inc_2_st.x += 1;
    st->inc_st.inc_2_st.y += 1;
    break;
  default:
    return 1/0;
  }
  return 0;
}
