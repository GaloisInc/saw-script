#include <stdio.h>
#include <stdint.h>
#include "simon.h"

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;

static u8 z[62] =
{1,1,0,1,1,0,1,1,1,0,1,0,1,1,0,0,0,1,1,0,0,1,0,1,1,1,1,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,1,0,0,1,1,1,0,0,1,1,0,1,0,0,0,0,1,1,1,1};

void KeyExpansion ( u32 k[] )
{
    u8 i;
    u32 tmp;
    for ( i=4 ; i<44 ; i++ )
    {
        tmp = ROTATE_RIGHT_32(k[i-1],3);
        tmp = tmp ^ k[i-3];
        tmp = tmp ^ ROTATE_RIGHT_32(tmp,1);
        k[i] = ~k[i-4] ^ tmp ^ z[i-4] ^ 3;
    }
}

void Encrypt ( u32 text[], u32 crypt[], u32 key[] )
{
    KeyExpansion(key);
    
    u8 i;
    u32 tmp;
    crypt[0] = text[0];
    crypt[1] = text[1];

    for ( i=0 ; i<44 ; i++ )
    {
        tmp = crypt[0];
        crypt[0] = crypt[1] ^ ((ROTATE_LEFT_32(crypt[0],1)) & (ROTATE_LEFT_32(crypt[0],8))) ^ (ROTATE_LEFT_32(crypt[0],2)) ^ key[i];
        crypt[1] = tmp;
    }
}

void Decrypt ( u32 text[], u32 crypt[], u32 key[] )
{
    KeyExpansion(key);

    u8 i;
    u32 tmp;
    crypt[0] = text[0];
    crypt[1] = text[1];

    for ( i=0 ; i<44 ; i++ )
    {
        tmp = crypt[1];
        crypt[1] = crypt[0] ^ ((ROTATE_LEFT_32(crypt[1],1)) & (ROTATE_LEFT_32(crypt[1],8))) ^ (ROTATE_LEFT_32(crypt[1],2)) ^ key[43-i];
        crypt[0] = tmp;
    }
}

int main ()
{

    u32 text[2];
    text[0] = 0x656b696c;
    text[1] = 0x20646e75;
    u32 crypt[2] = {0};
    u32 k[44], k2[44];
    k[3] = k2[3] = 0x1b1a1918;
    k[2] = k2[2] = 0x13121110;
    k[1] = k2[1] = 0x0b0a0908;
    k[0] = k2[0] = 0x03020100;
    KeyExpansion ( k );



    Encrypt ( text, crypt, k );
    printf("%x %x\n%x %x\n\n\n", text[0], text[1], crypt[0], crypt[1]);
    Decrypt ( crypt, text, k2 );
    printf("%x %x\n%x %x\n\n\n", text[0], text[1], crypt[0], crypt[1]);

    return 0;
}
