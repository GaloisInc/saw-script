/*
** Portable ChaCha20/8 implementation. Based on RFC 7539.
** Copyright (C) 2015-2016 Austin Seipp. Released in the Public Domain.
*/

#ifndef _CRYPTO_CHACHA20_H_
#define _CRYPTO_CHACHA20_H_

#ifdef __cplusplus
extern "C" {
#endif

#define crypto_stream_chacha20_KEYBYTES   32
#define crypto_stream_chacha20_NONCEBYTES 12

int
crypto_stream_chacha20_xor(unsigned char* out,
                           const unsigned char* msg,
                           unsigned long long mlen,
                           const unsigned int counter,
                           const unsigned char* nonce,
                           const unsigned char* key);

int
crypto_stream_chacha20(unsigned char* out,
                       unsigned long long olen,
                       unsigned int counter,
                       const unsigned char* nonce,
                       const unsigned char* key);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* !_CRYPTO_CHACHA20_H_ */
