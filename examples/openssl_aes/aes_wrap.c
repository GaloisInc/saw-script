#include <openssl/aes.h>

// A wrapper to make OpenSSL's AES work in one pass, like the Cryptol
// specification.
int aes_encrypt(const unsigned char *in,
                unsigned char *out,
                const unsigned char *key) {
  AES_KEY rkey;
  int r = AES_set_encrypt_key(key, 128, &rkey);
  AES_encrypt(in, out, &rkey);
  return r;
}
