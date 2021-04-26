#include <emmintrin.h>
#include <wmmintrin.h>
#include <tmmintrin.h>
#include <stdio.h>
#include <stdint.h>

void printBytes (unsigned char* byte_array, int bytes){
  int i=0;
  while (i < bytes)
  {
      printf("%02X",(unsigned)byte_array[i]);
      i++;
      if(i%2 == 0) printf(" ");
      if(i%4== 0) printf("\n");
  }
  printf("\n");
}

int main(int argc, char *argv[])
{
  __m128i vector;
  __m128i final_vector;
  __m128i* vector2 = malloc(128);
  int32_t array[4] = {1442454,2242865,3676852,4486525};
  int32_t final_array[4] = { 0xED16D184, 0x4CE73AC3, 0x3F672DCC, 0x00002837 };

  vector = _mm_setr_epi32(1442454,2242865,3676852,4486525);
  final_vector = _mm_loadu_si128( (__m128i*) &final_array );

  //printBytes((unsigned char *)&array, 16);
  //printBytes((unsigned char *)&vector, 16);

  _mm_storeu_si128(vector2, vector);
  vector = _mm_loadu_si128(vector2);
  //printBytes((unsigned char *)&vector, 16);

  *vector2 = _mm_xor_si128 (vector, vector);
  //printBytes((unsigned char *)vector2, 16);

  *vector2 = vector + vector + vector;
  //printBytes((unsigned char *)vector2, 16);

  vector = _mm_clmulepi64_si128(vector, *vector2, 0x00);
  vector = _mm_clmulepi64_si128(vector, *vector2, 0x01);
  vector = _mm_clmulepi64_si128(vector, *vector2, 0x10);
  vector = _mm_clmulepi64_si128(vector, *vector2, 0x11);
  
  int result = (vector[0] == final_vector[0]) && (vector[1] == final_vector[1]);

  //printBytes((unsigned char *)&vector, 16);
  //printBytes((unsigned char *)&final_vector, 16);

  vector = _mm_slli_si128(vector, 2);
  //printBytes((unsigned char *)&vector, 16);

  vector = _mm_srli_si128(vector, 2);
  // printBytes((unsigned char *)&vector, 16);

  vector = _mm_shuffle_epi32(vector, 78);
  //printBytes((unsigned char *)&vector, 16);

  //printBytes((unsigned char *)&vector, 16);

  return !result;
}
