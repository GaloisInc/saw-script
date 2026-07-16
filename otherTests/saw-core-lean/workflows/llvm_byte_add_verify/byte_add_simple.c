/* Straight-line 4-byte carry-chain adder: the byte-decomposition
   content of SV-COMP byte_add without its na/nb early-termination
   branch tower (which explodes symbolic execution into a ~700K-line
   emitted goal). Same lemma family: add/carry/shl/trunc/zext. */
unsigned int mp_add_simple(unsigned int a, unsigned int b)
{
    unsigned char a0 = a, a1 = a >> 8, a2 = a >> 16, a3 = a >> 24;
    unsigned char b0 = b, b1 = b >> 8, b2 = b >> 16, b3 = b >> 24;
    unsigned short s0 = (unsigned short)a0 + b0;
    unsigned char r0 = (unsigned char)s0;
    unsigned short s1 = (unsigned short)a1 + b1 + (s0 >> 8);
    unsigned char r1 = (unsigned char)s1;
    unsigned short s2 = (unsigned short)a2 + b2 + (s1 >> 8);
    unsigned char r2 = (unsigned char)s2;
    unsigned short s3 = (unsigned short)a3 + b3 + (s2 >> 8);
    unsigned char r3 = (unsigned char)s3;
    return (unsigned int)r0 | ((unsigned int)r1 << 8)
         | ((unsigned int)r2 << 16) | ((unsigned int)r3 << 24);
}
