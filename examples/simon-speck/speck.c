/*
 * Speck cipher implementation and testing code
 * (c) 2013 by Sebastian Gesemann
 *
 * Speck is a family of lightweight block ciphers designed by a team
 * of NSA members (see http://eprint.iacr.org/2013/404.pdf )
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

 
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>


// Configuration / Selecting a member from the Speck family

#ifndef N
#define N 32 // bits per word, only 32 and 64 are supported
#endif

#ifndef M
#define M (144/N)  // words per key
#endif

#ifndef R    // rounds per en-/decryption
#if N==32
#define R (23+M)
#elif N==64
#define R (30+M)
#else
#error "number of rounds not given"
#endif
#endif


// Checking config parameters

#if N==32
typedef uint32_t word_t;
#elif N==64
typedef uint64_t word_t;
#else
#error "only word sizes 32 and 64 are supported"
#endif

#if M<2 || M>4 || (M==2 && N==32)
#error "invalid number of key words"
#endif

#if R<M
#error "too few rounds"
#endif


// Speck key schedule, encryption, decryption

#define LCS(x,n) (((x) << (n)) | ((x) >> (N-(n))))
#define RCS(x,n) (((x) >> (n)) | ((x) << (N-(n))))
#if N>=24
#define     ROUND(x,y,k) (x=RCS(x,8), x+=y, x^=k, y=LCS(y,3), y^=x)
#define INV_ROUND(x,y,k) (y^=x, y=RCS(y,3), x^=k, x-=y, x=LCS(x,8))
#else
#error "cyclic shifts in round function are incorrect for this word size"
#endif

/// expands a key of M words into R round keys in-place
void speck_keyexpand(word_t K[])
{
	word_t tmp[M], *p;
	memcpy(tmp,K,sizeof tmp);
	// K[0] stays the same
	for (int i=0; i<(R-1);) {
		p = tmp + (1+(i%(M-1)));
		ROUND(*p,tmp[0],i);
		++i;
		K[i] = tmp[0];
	}
}

/// encrypts block in-place given the round keys
void speck_encrypt(word_t io[2], word_t xK[])
{
    speck_keyexpand(xK);
	for (int i=0; i<R; ++i) {
		ROUND(io[1],io[0],xK[i]);
	}
}

/// decrypts block in-place given the round keys
void speck_decrypt(word_t io[2], word_t xK[])
{
    speck_keyexpand(xK);
	for (int i=R; i-->0;) {
		INV_ROUND(io[1],io[0],xK[i]);
	}
}

// Test program ...
#ifndef SAW
void display(int n, const word_t data[])
{
	static const char hex[] = "0123456789abcdef";
	char temp[2+((N+3)/4)] = " ";
	for (int i=n; i-->0;) {
		word_t tmp = data[i];
		for (int k=0; k<((N+3)/4); ++k) {
			temp[((N+3)/4)-k] = hex[tmp & 0xF];
			tmp >>= 4;
		}
		printf("%s",temp+(i+1==n));
	}
	puts("");
}

/// tests the given test vector
/// @return 0=ok, 1=encryption error, 2=decryption error
#if N==32 && M==4
int test_test_vector(void)
{
	static const word_t p[2] = {0x7475432d, 0x3b726574};
	static const word_t c[2] = {0x454e028b, 0x8c6fa548};
	word_t k[R] = {0x03020100, 0x0b0a0908, 0x13121110, 0x1b1a1918};
	word_t k2[R] = {0x03020100, 0x0b0a0908, 0x13121110, 0x1b1a1918};
	word_t io[] = {p[0],p[1]};
	speck_encrypt(io,k);
	if (io[0]!=c[0] || io[1]!=c[1]) {
		puts("encryption error");
		return 1;
	}
	puts("encryption ok");
	speck_decrypt(io,k2);
	if (io[0]!=p[0] || io[1]!=p[1]) {
		puts("decryption error");
		return 2;
	}
	puts("decryption ok");
	return 0;
}
//[0x0F0E0D0C0B0A0908, 0x0706050403020100] (0x6C61766975716520, 0x7469206564616D20) == (0xA65D985179783265, 0x7860FEDF5C570D18)
#else
int test_test_vector(void)
{
	static const word_t p[2] = {0x7469206564616D20ULL, 0x6C61766975716520ULL};
	static const word_t c[2] = {0x7860FEDF5C570D18ULL, 0xA65D985179783265ULL};
	word_t k[R] = {0x0706050403020100ULL, 0x0F0E0D0C0B0A0908ULL};
	word_t k2[R] = {0x0706050403020100ULL, 0x0F0E0D0C0B0A0908ULL};
	word_t io[] = {p[0],p[1]};
	speck_encrypt(io,k);
	if (io[0]!=c[0] || io[1]!=c[1]) {
		puts("encryption error");
		return 1;
	}
	puts("encryption ok");
	speck_decrypt(io,k2);
	if (io[0]!=p[0] || io[1]!=p[1]) {
		puts("decryption error");
		return 2;
	}
	puts("decryption ok");
	return 0;
}
#endif

#if N==32
int count_set_bits(word_t t)
{
	t = ((t & 0xAAAAAAAA) >> 1) + (t & 0x55555555);
	t = ((t & 0xCCCCCCCC) >> 2) + (t & 0x33333333);
	t = ((t & 0xF0F0F0F0) >> 4) + (t & 0x0F0F0F0F);
	t += t >> 16;
	t += t >> 8;
	return t & 0xFF;
}
#elif N==64
int count_set_bits(word_t t)
{
	t = ((t & 0xAAAAAAAAAAAAAAAAu) >> 1) + (t & 0x5555555555555555u);
	t = ((t & 0xCCCCCCCCCCCCCCCCu) >> 2) + (t & 0x3333333333333333u);
	t = ((t & 0xF0F0F0F0F0F0F0F0u) >> 4) + (t & 0x0F0F0F0F0F0F0F0Fu);
	t += t >> 32;
	t += t >> 16;
	t += t >> 8;
	return t & 0xFF;
}
#endif

word_t rand_word(void)
{
	word_t result = 0;
	#if N % 8
	#error "expected word size to be dividable by 8"
	#endif
	for (int i=0; i<N; i+=8) {
		result = (result << 8) | (rand() & 0xFFu);
	}
	return result;
}

static int test_confusion_once(void)
{
	word_t kA[R];
	word_t kB[R];
	word_t ioA[2];
	word_t ioB[2];
	for (int i=0; i<M; ++i)
		kA[i] = kB[i] = rand_word();
	#if N & (N-1)
	#error "I actually expect N to be a power of two"
	#else
	kB[rand() % M] ^= ((word_t)1u) << (rand() & (N-1));
	#endif
	for (int i=0; i<2; ++i) {
		ioA[i] = ioB[i] = rand_word();
	}
	speck_encrypt(ioA,kA);
	speck_encrypt(ioB,kB);
	int result = 0;
	for (int i=0; i<2; ++i)
		result += count_set_bits(ioA[i]^ioB[i]);
	return result;
}

int test_diffusion_once(void)
{
	word_t k[R];
	word_t k2[R];
	word_t ioA[2];
	word_t ioB[2];
	for (int i=0; i<M; ++i)
		k2[i] = k[i] = rand_word();
	for (int i=0; i<2; ++i) {
		ioA[i] = ioB[i] = rand_word();
	}
	#if N & (N-1)
	#error "I actually expect N to be a power of two"
	#else
	ioB[rand()&1] ^= ((word_t)1u) << (rand() & (N-1));
	#endif
	speck_encrypt(ioA,k);
	speck_encrypt(ioB,k2);
	int result = 0;
	for (int i=0; i<2; ++i)
		result += count_set_bits(ioA[i]^ioB[i]);
	return result;
}

/// estimates the mean and variance of a distribution
/// from a given histogram
void compute_mean_and_vari_from_hist(
	int slots, const unsigned long counts[],
	double *pmean, double *pvari)
{
	unsigned long long sum0 = 0;
	unsigned long long sum1 = 0;
	for (int i=0; i<slots; ++i) {
		unsigned long long tmp = counts[i];
		sum0 += tmp;
		sum1 += tmp * i;
	}
	*pmean = (double)sum1 / (double)sum0;
	double sum2 = 0;
	for (int i=0; i<slots; ++i) {
		unsigned long tmp = counts[i];
		double delta = i - *pmean;
		sum2 += tmp * delta*delta;
	}
	*pvari = sum2/(sum0-1);
}

void test(const char* what, int (*pfun)(void))
{
	unsigned long histogram[N*2+1] = {0};
	for (unsigned long pass=0; pass<1222333; ++pass) {
		int hd = pfun();
		if (0<=hd && hd<=(N*2)) {
			histogram[hd]++;
		} else {
			puts("unexpected output difference, internal error");
			abort();
		}
	}
	double m, v;
	compute_mean_and_vari_from_hist(N*2+1,histogram,&m,&v);
	printf("Speck-%d-%d [nr=%d], %s test: mean=%f, variance=%f\n",2*N,M*N,R,what,m,v);
}

int main(void)
{
	srand(time(0));
	test("confusion",test_confusion_once);
	test("diffusion",test_diffusion_once);
	return test_test_vector();
}
#endif