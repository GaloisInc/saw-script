#include <stdio.h>
#include <stdint.h>
#include "simon.h"

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint64_t u64;

static u8 z[62] =
{1,0,1,0,1,1,1,1,0,1,1,1,0,0,0,0,0,0,1,1,0,1,0,0,1,0,0,1,1,0,0,0,1,0,1,0,0,0,0,1,0,0,0,1,1,1,1,1,1,0,0,1,0,1,1,0,1,1,0,0,1,1};

void KeyExpansion ( u64 k[] )
{
    u8 i;
    u64 tmp;
    for ( i=2 ; i<64 ; i++ )
    {
        tmp = ROTATE_RIGHT_64(k[i-1],3);
        tmp = tmp ^ ROTATE_RIGHT_64(tmp,1);
        k[i] = ~k[i-2] ^ tmp ^ z[(i-2)] ^ 3;
    }
    for ( i=64 ; i<68 ; i++ )
    {
        tmp = ROTATE_RIGHT_64(k[i-1],3);
        tmp = tmp ^ ROTATE_RIGHT_64(tmp,1);
        k[i] = ~k[i-2] ^ tmp ^ z[(i-2)-62] ^ 3;
    }
}

void Encrypt ( u64 text[], u64 crypt[], u64 key[] )
{
    KeyExpansion(key);
    
    u8 i;
    u64 tmp;
    crypt[0] = text[0];
    crypt[1] = text[1];

    for ( i=0 ; i<68 ; i++ )
    {
        tmp = crypt[0];
        crypt[0] = crypt[1] ^ ((ROTATE_LEFT_64(crypt[0],1)) & (ROTATE_LEFT_64(crypt[0],8))) ^ (ROTATE_LEFT_64(crypt[0],2)) ^ key[i];
        crypt[1] = tmp;
    }
}

void Decrypt ( u64 text[], u64 crypt[], u64 key[] )
{
    KeyExpansion(key);
    
    u8 i;
    u64 tmp;
    crypt[0] = text[0];
    crypt[1] = text[1];

    for ( i=0 ; i<68 ; i++ )
    {
        tmp = crypt[1];
        crypt[1] = crypt[0] ^ ((ROTATE_LEFT_64(crypt[1],1)) & (ROTATE_LEFT_64(crypt[1],8))) ^ (ROTATE_LEFT_64(crypt[1],2)) ^ key[67-i];
        crypt[0] = tmp;
    }
}

int main ()
{

    u64 text[2];
    text[0] = 0x6373656420737265;
    text[1] = 0x6c6c657661727420;
    u64 crypt[2] = {0};
    u64 k[68], k2[68];
    k[1] = k2[1] = 0x0f0e0d0c0b0a0908;
    k[0] = k2[0] = 0x0706050403020100;

    Encrypt ( text, crypt, k );
    printf("%llx %llx\n%llx %llx\n\n\n", text[0], text[1], crypt[0], crypt[1]);
	Decrypt ( crypt, text, k );
    printf("%llx %llx\n%llx %llx\n\n\n", text[0], text[1], crypt[0], crypt[1]);

    return 0;
}
