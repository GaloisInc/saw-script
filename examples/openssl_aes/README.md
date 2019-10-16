This directory includes a proof of equivalence between a Cryptol
specification of AES and the implementation included in OpenSSL.
The `Makefile` in this directory automatically downloads and compiles
OpenSSL, and then extracts the relevant LLVM bitcode file.

Because the OpenSSL implementation uses a separate function to expand
the key and then perform encryption, while the Cryptol specification
uses a single function from the plaintext and key to a ciphertext, we
include a wrapper to do key expansion followed by encryption:

~~~~{.c}
int aes_encrypt(const unsigned char *in,
                unsigned char *out,
                const unsigned char *key) {
  AES_KEY rkey;
  int r = private_AES_set_encrypt_key(key, 128, &rkey);
  AES_encrypt(in, out, &rkey);
  return r;
}
~~~~
