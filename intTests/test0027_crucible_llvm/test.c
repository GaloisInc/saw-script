#include <stdlib.h>
#include <stdio.h>

uint32_t add_nums32( uint32_t x, uint32_t y ) {
  return (x+y);
}

uint64_t add_nums64( uint64_t x, uint64_t y ) {
  return (x+y);
}

int main() {
  printf("%u + %u = %u\n", 12U, 30U, add_nums32( 12U, 30U ) );
  printf("%llu + %llu = %llu\n", 12ULL, 30ULL, add_nums64( 12ULL, 30ULL ) );
  return 0;
}
