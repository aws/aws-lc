#ifndef KEM_KYBER_H
#define KEM_KYBER_H

#include <stddef.h>
#include <stdint.h>
#include <openssl/base.h>
#include <openssl/evp.h>

#define KYBER512_PRIVATE_KEY_BYTES 1632
#define KYBER512_PUBLIC_KEY_BYTES 800
#define KYBER512_KEM_CIPHERTEXT_BYTES 768
#define KYBER512_KEM_SHARED_SECRET_BYTES 32

int kyber512_keypair(uint8_t *public_key, uint8_t *secret_key);

int kyber512_encapsulate_init(void *ctx,
                              void *prov_key,
                              const OSSL_PARAM params[]);
int kyber512_encapsulate(void *ctx,
                         unsigned char *out,
                         size_t *out_len,
                         unsigned char *secret,
                         size_t *secret_len);
int kyber512_decapsulate_init(void *ctx,
                              void *prov_key,
                              const OSSL_PARAM params[]);
int kyber512_decapsulate(void *ctx,
                         unsigned char *out,
                         size_t *out_len,
                         const unsigned char *in,
                         size_t in_len);

#endif

