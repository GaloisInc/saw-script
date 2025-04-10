// ============================================================================
// The code in this file is based off of that in:
// https://github.com/awslabs/aws-lc/
// (commit: d84d2f329dccbc7f3866eab54951bd012e317041)
// ============================================================================

#include <stdlib.h>
#include <stdint.h>
#include <string.h>

// ============================================================================
// Helper functions from crypto/internal.h
// ============================================================================

static inline void *OPENSSL_memcpy(void *dst, const void *src, size_t n) {
  if (n == 0) {
    return dst;
  }

  return memcpy(dst, src, n);
}

static inline uint32_t CRYPTO_bswap4(uint32_t x) {
  x = (x >> 16) | (x << 16);
  x = ((x & 0xff00ff00) >> 8) | ((x & 0x00ff00ff) << 8);
  return x;
}

static inline uint64_t CRYPTO_bswap8(uint64_t x) {
  return CRYPTO_bswap4(x >> 32) | (((uint64_t)CRYPTO_bswap4(x)) << 32);
}

static inline uint64_t CRYPTO_load_u64_be(const void *ptr) {
  uint64_t ret;
  OPENSSL_memcpy(&ret, ptr, sizeof(ret));
  return CRYPTO_bswap8(ret);
}

// ============================================================================
// The defintion of sha512_block_data_order from crypto/fipsmodule/sha/sha512.c
// with only one addition (return_state), needed for Heapster typechecking 
// ============================================================================

// Used in sha512_block_data_order below, needed for Heapster typechecking
void return_state(uint64_t *state) { }

static const uint64_t K512[80] = {
    UINT64_C(0x428a2f98d728ae22), UINT64_C(0x7137449123ef65cd),
    UINT64_C(0xb5c0fbcfec4d3b2f), UINT64_C(0xe9b5dba58189dbbc),
    UINT64_C(0x3956c25bf348b538), UINT64_C(0x59f111f1b605d019),
    UINT64_C(0x923f82a4af194f9b), UINT64_C(0xab1c5ed5da6d8118),
    UINT64_C(0xd807aa98a3030242), UINT64_C(0x12835b0145706fbe),
    UINT64_C(0x243185be4ee4b28c), UINT64_C(0x550c7dc3d5ffb4e2),
    UINT64_C(0x72be5d74f27b896f), UINT64_C(0x80deb1fe3b1696b1),
    UINT64_C(0x9bdc06a725c71235), UINT64_C(0xc19bf174cf692694),
    UINT64_C(0xe49b69c19ef14ad2), UINT64_C(0xefbe4786384f25e3),
    UINT64_C(0x0fc19dc68b8cd5b5), UINT64_C(0x240ca1cc77ac9c65),
    UINT64_C(0x2de92c6f592b0275), UINT64_C(0x4a7484aa6ea6e483),
    UINT64_C(0x5cb0a9dcbd41fbd4), UINT64_C(0x76f988da831153b5),
    UINT64_C(0x983e5152ee66dfab), UINT64_C(0xa831c66d2db43210),
    UINT64_C(0xb00327c898fb213f), UINT64_C(0xbf597fc7beef0ee4),
    UINT64_C(0xc6e00bf33da88fc2), UINT64_C(0xd5a79147930aa725),
    UINT64_C(0x06ca6351e003826f), UINT64_C(0x142929670a0e6e70),
    UINT64_C(0x27b70a8546d22ffc), UINT64_C(0x2e1b21385c26c926),
    UINT64_C(0x4d2c6dfc5ac42aed), UINT64_C(0x53380d139d95b3df),
    UINT64_C(0x650a73548baf63de), UINT64_C(0x766a0abb3c77b2a8),
    UINT64_C(0x81c2c92e47edaee6), UINT64_C(0x92722c851482353b),
    UINT64_C(0xa2bfe8a14cf10364), UINT64_C(0xa81a664bbc423001),
    UINT64_C(0xc24b8b70d0f89791), UINT64_C(0xc76c51a30654be30),
    UINT64_C(0xd192e819d6ef5218), UINT64_C(0xd69906245565a910),
    UINT64_C(0xf40e35855771202a), UINT64_C(0x106aa07032bbd1b8),
    UINT64_C(0x19a4c116b8d2d0c8), UINT64_C(0x1e376c085141ab53),
    UINT64_C(0x2748774cdf8eeb99), UINT64_C(0x34b0bcb5e19b48a8),
    UINT64_C(0x391c0cb3c5c95a63), UINT64_C(0x4ed8aa4ae3418acb),
    UINT64_C(0x5b9cca4f7763e373), UINT64_C(0x682e6ff3d6b2b8a3),
    UINT64_C(0x748f82ee5defb2fc), UINT64_C(0x78a5636f43172f60),
    UINT64_C(0x84c87814a1f0ab72), UINT64_C(0x8cc702081a6439ec),
    UINT64_C(0x90befffa23631e28), UINT64_C(0xa4506cebde82bde9),
    UINT64_C(0xbef9a3f7b2c67915), UINT64_C(0xc67178f2e372532b),
    UINT64_C(0xca273eceea26619c), UINT64_C(0xd186b8c721c0c207),
    UINT64_C(0xeada7dd6cde0eb1e), UINT64_C(0xf57d4f7fee6ed178),
    UINT64_C(0x06f067aa72176fba), UINT64_C(0x0a637dc5a2c898a6),
    UINT64_C(0x113f9804bef90dae), UINT64_C(0x1b710b35131c471b),
    UINT64_C(0x28db77f523047d84), UINT64_C(0x32caab7b40c72493),
    UINT64_C(0x3c9ebe0a15c9bebc), UINT64_C(0x431d67c49c100d4c),
    UINT64_C(0x4cc5d4becb3e42b6), UINT64_C(0x597f299cfc657e2a),
    UINT64_C(0x5fcb6fab3ad6faec), UINT64_C(0x6c44198c4a475817),
};

#define ROTR(x, s) (((x) >> s) | (x) << (64 - s))

#define Sigma0(x) (ROTR((x), 28) ^ ROTR((x), 34) ^ ROTR((x), 39))
#define Sigma1(x) (ROTR((x), 14) ^ ROTR((x), 18) ^ ROTR((x), 41))
#define sigma0(x) (ROTR((x), 1) ^ ROTR((x), 8) ^ ((x) >> 7))
#define sigma1(x) (ROTR((x), 19) ^ ROTR((x), 61) ^ ((x) >> 6))

#define Ch(x, y, z) (((x) & (y)) ^ ((~(x)) & (z)))
#define Maj(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))

#define ROUND_00_15(i, a, b, c, d, e, f, g, h)   \
  do {                                           \
    T1 += h + Sigma1(e) + Ch(e, f, g) + K512[i]; \
    h = Sigma0(a) + Maj(a, b, c);                \
    d += T1;                                     \
    h += T1;                                     \
  } while (0)

#define ROUND_16_80(i, j, a, b, c, d, e, f, g, h, X)   \
  do {                                                 \
    s0 = X[(j + 1) & 0x0f];                            \
    s0 = sigma0(s0);                                   \
    s1 = X[(j + 14) & 0x0f];                           \
    s1 = sigma1(s1);                                   \
    T1 = X[(j) & 0x0f] += s0 + s1 + X[(j + 9) & 0x0f]; \
    ROUND_00_15(i + j, a, b, c, d, e, f, g, h);        \
  } while (0)

static void sha512_block_data_order(uint64_t *state, const uint8_t *in,
                                    size_t num) {
  uint64_t a, b, c, d, e, f, g, h, s0, s1, T1;
  uint64_t X[16];
  int i;

  while (num--) {

    a = state[0];
    b = state[1];
    c = state[2];
    d = state[3];
    e = state[4];
    f = state[5];
    g = state[6];
    h = state[7];
    return_state(state); // for Heapster

    T1 = X[0] = CRYPTO_load_u64_be(in);
    ROUND_00_15(0, a, b, c, d, e, f, g, h);
    T1 = X[1] = CRYPTO_load_u64_be(in + 8);
    ROUND_00_15(1, h, a, b, c, d, e, f, g);
    T1 = X[2] = CRYPTO_load_u64_be(in + 2 * 8);
    ROUND_00_15(2, g, h, a, b, c, d, e, f);
    T1 = X[3] = CRYPTO_load_u64_be(in + 3 * 8);
    ROUND_00_15(3, f, g, h, a, b, c, d, e);
    T1 = X[4] = CRYPTO_load_u64_be(in + 4 * 8);
    ROUND_00_15(4, e, f, g, h, a, b, c, d);
    T1 = X[5] = CRYPTO_load_u64_be(in + 5 * 8);
    ROUND_00_15(5, d, e, f, g, h, a, b, c);
    T1 = X[6] = CRYPTO_load_u64_be(in + 6 * 8);
    ROUND_00_15(6, c, d, e, f, g, h, a, b);
    T1 = X[7] = CRYPTO_load_u64_be(in + 7 * 8);
    ROUND_00_15(7, b, c, d, e, f, g, h, a);
    T1 = X[8] = CRYPTO_load_u64_be(in + 8 * 8);
    ROUND_00_15(8, a, b, c, d, e, f, g, h);
    T1 = X[9] = CRYPTO_load_u64_be(in + 9 * 8);
    ROUND_00_15(9, h, a, b, c, d, e, f, g);
    T1 = X[10] = CRYPTO_load_u64_be(in + 10 * 8);
    ROUND_00_15(10, g, h, a, b, c, d, e, f);
    T1 = X[11] = CRYPTO_load_u64_be(in + 11 * 8);
    ROUND_00_15(11, f, g, h, a, b, c, d, e);
    T1 = X[12] = CRYPTO_load_u64_be(in + 12 * 8);
    ROUND_00_15(12, e, f, g, h, a, b, c, d);
    T1 = X[13] = CRYPTO_load_u64_be(in + 13 * 8);
    ROUND_00_15(13, d, e, f, g, h, a, b, c);
    T1 = X[14] = CRYPTO_load_u64_be(in + 14 * 8);
    ROUND_00_15(14, c, d, e, f, g, h, a, b);
    T1 = X[15] = CRYPTO_load_u64_be(in + 15 * 8);
    ROUND_00_15(15, b, c, d, e, f, g, h, a);

    for (i = 16; i < 80; i += 16) {
      ROUND_16_80(i, 0, a, b, c, d, e, f, g, h, X);
      ROUND_16_80(i, 1, h, a, b, c, d, e, f, g, X);
      ROUND_16_80(i, 2, g, h, a, b, c, d, e, f, X);
      ROUND_16_80(i, 3, f, g, h, a, b, c, d, e, X);
      ROUND_16_80(i, 4, e, f, g, h, a, b, c, d, X);
      ROUND_16_80(i, 5, d, e, f, g, h, a, b, c, X);
      ROUND_16_80(i, 6, c, d, e, f, g, h, a, b, X);
      ROUND_16_80(i, 7, b, c, d, e, f, g, h, a, X);
      ROUND_16_80(i, 8, a, b, c, d, e, f, g, h, X);
      ROUND_16_80(i, 9, h, a, b, c, d, e, f, g, X);
      ROUND_16_80(i, 10, g, h, a, b, c, d, e, f, X);
      ROUND_16_80(i, 11, f, g, h, a, b, c, d, e, X);
      ROUND_16_80(i, 12, e, f, g, h, a, b, c, d, X);
      ROUND_16_80(i, 13, d, e, f, g, h, a, b, c, X);
      ROUND_16_80(i, 14, c, d, e, f, g, h, a, b, X);
      ROUND_16_80(i, 15, b, c, d, e, f, g, h, a, X);
    }

    state[0] += a;
    state[1] += b;
    state[2] += c;
    state[3] += d;
    state[4] += e;
    state[5] += f;
    state[6] += g;
    state[7] += h;

    in += 16 * 8;
  }
}


// ============================================================================
// A definition equivalent to sha512_block_data_order which uses multiple
// functions, for use with Mr. Solver
// ============================================================================

static void round_00_15(uint64_t i,
                        uint64_t *a, uint64_t *b, uint64_t *c, uint64_t *d,
                        uint64_t *e, uint64_t *f, uint64_t *g, uint64_t *h,
                        uint64_t *T1) {
  *T1 += *h + Sigma1(*e) + Ch(*e, *f, *g) + K512[i];
  *h = Sigma0(*a) + Maj(*a, *b, *c);
  *d += *T1;
  *h += *T1;
}

static void round_16_80(uint64_t i, uint64_t j,
                        uint64_t *a, uint64_t *b, uint64_t *c, uint64_t *d,
                        uint64_t *e, uint64_t *f, uint64_t *g, uint64_t *h,
                        uint64_t *X,
                        uint64_t* s0, uint64_t *s1, uint64_t *T1) {
  *s0 = X[(j + 1) & 0x0f];
  *s0 = sigma0(*s0);
  *s1 = X[(j + 14) & 0x0f];
  *s1 = sigma1(*s1);
  *T1 = X[(j) & 0x0f] += *s0 + *s1 + X[(j + 9) & 0x0f];
  round_00_15(i + j, a, b, c, d, e, f, g, h, T1);
}

// Used in processBlock below, needed for Heapster typechecking
void return_X(uint64_t *X) { }

static void processBlock(uint64_t *a, uint64_t *b, uint64_t *c, uint64_t *d,
                         uint64_t *e, uint64_t *f, uint64_t *g, uint64_t *h,
                         const uint8_t *in) {
  uint64_t s0, s1, T1;
  uint64_t X[16];
  uint64_t i;
  
  T1 = X[0] = CRYPTO_load_u64_be(in);
  round_00_15(0, a, b, c, d, e, f, g, h, &T1);
  T1 = X[1] = CRYPTO_load_u64_be(in + 8);
  round_00_15(1, h, a, b, c, d, e, f, g, &T1);
  T1 = X[2] = CRYPTO_load_u64_be(in + 2 * 8);
  round_00_15(2, g, h, a, b, c, d, e, f, &T1);
  T1 = X[3] = CRYPTO_load_u64_be(in + 3 * 8);
  round_00_15(3, f, g, h, a, b, c, d, e, &T1);
  T1 = X[4] = CRYPTO_load_u64_be(in + 4 * 8);
  round_00_15(4, e, f, g, h, a, b, c, d, &T1);
  T1 = X[5] = CRYPTO_load_u64_be(in + 5 * 8);
  round_00_15(5, d, e, f, g, h, a, b, c, &T1);
  T1 = X[6] = CRYPTO_load_u64_be(in + 6 * 8);
  round_00_15(6, c, d, e, f, g, h, a, b, &T1);
  T1 = X[7] = CRYPTO_load_u64_be(in + 7 * 8);
  round_00_15(7, b, c, d, e, f, g, h, a, &T1);
  T1 = X[8] = CRYPTO_load_u64_be(in + 8 * 8);
  round_00_15(8, a, b, c, d, e, f, g, h, &T1);
  T1 = X[9] = CRYPTO_load_u64_be(in + 9 * 8);
  round_00_15(9, h, a, b, c, d, e, f, g, &T1);
  T1 = X[10] = CRYPTO_load_u64_be(in + 10 * 8);
  round_00_15(10, g, h, a, b, c, d, e, f, &T1);
  T1 = X[11] = CRYPTO_load_u64_be(in + 11 * 8);
  round_00_15(11, f, g, h, a, b, c, d, e, &T1);
  T1 = X[12] = CRYPTO_load_u64_be(in + 12 * 8);
  round_00_15(12, e, f, g, h, a, b, c, d, &T1);
  T1 = X[13] = CRYPTO_load_u64_be(in + 13 * 8);
  round_00_15(13, d, e, f, g, h, a, b, c, &T1);
  T1 = X[14] = CRYPTO_load_u64_be(in + 14 * 8);
  round_00_15(14, c, d, e, f, g, h, a, b, &T1);
  T1 = X[15] = CRYPTO_load_u64_be(in + 15 * 8);
  round_00_15(15, b, c, d, e, f, g, h, a, &T1);

  return_X(X); // for Heapster

  for (i = 16; i < 80; i += 16) {
    round_16_80(i, 0, a, b, c, d, e, f, g, h, X, &s0, &s1, &T1);
    round_16_80(i, 1, h, a, b, c, d, e, f, g, X, &s0, &s1, &T1);
    round_16_80(i, 2, g, h, a, b, c, d, e, f, X, &s0, &s1, &T1);
    round_16_80(i, 3, f, g, h, a, b, c, d, e, X, &s0, &s1, &T1);
    round_16_80(i, 4, e, f, g, h, a, b, c, d, X, &s0, &s1, &T1);
    round_16_80(i, 5, d, e, f, g, h, a, b, c, X, &s0, &s1, &T1);
    round_16_80(i, 6, c, d, e, f, g, h, a, b, X, &s0, &s1, &T1);
    round_16_80(i, 7, b, c, d, e, f, g, h, a, X, &s0, &s1, &T1);
    round_16_80(i, 8, a, b, c, d, e, f, g, h, X, &s0, &s1, &T1);
    round_16_80(i, 9, h, a, b, c, d, e, f, g, X, &s0, &s1, &T1);
    round_16_80(i, 10, g, h, a, b, c, d, e, f, X, &s0, &s1, &T1);
    round_16_80(i, 11, f, g, h, a, b, c, d, e, X, &s0, &s1, &T1);
    round_16_80(i, 12, e, f, g, h, a, b, c, d, X, &s0, &s1, &T1);
    round_16_80(i, 13, d, e, f, g, h, a, b, c, X, &s0, &s1, &T1);
    round_16_80(i, 14, c, d, e, f, g, h, a, b, X, &s0, &s1, &T1);
    round_16_80(i, 15, b, c, d, e, f, g, h, a, X, &s0, &s1, &T1);
  }
}

static void processBlocks(uint64_t *state, const uint8_t *in, size_t num) {
  uint64_t a, b, c, d, e, f, g, h;

  while (num--) {

    a = state[0];
    b = state[1];
    c = state[2];
    d = state[3];
    e = state[4];
    f = state[5];
    g = state[6];
    h = state[7];
    
    processBlock(&a, &b, &c, &d, &e, &f, &g, &h, in);
    
    state[0] += a;
    state[1] += b;
    state[2] += c;
    state[3] += d;
    state[4] += e;
    state[5] += f;
    state[6] += g;
    state[7] += h;

    in += 16 * 8;
  }
}


// Needed for Heapster to be able to see the static functions above
void dummy(uint64_t *state, const uint8_t *in, size_t num) {
  sha512_block_data_order(state, in, num);
  processBlocks(state, in, num);
}
