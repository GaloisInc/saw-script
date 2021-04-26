#include <stdint.h>

uint32_t popcount( uint32_t x ) {
  return __builtin_popcount( x );
}

uint32_t clz( uint32_t x ) {
  return x ? __builtin_clz( x ) : 32;
}

uint32_t ctz( uint32_t x ) {
  return x ? __builtin_ctz( x ) : 32;
}
