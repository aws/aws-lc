#ifndef _PQ_KEM_H_
#define _PQ_KEM_H_

#include <stdint.h>
#include "openssl/base.h"

#define KYBER512_SECRET_KEY_BYTES 1632
#define KYBER512_PUBLIC_KEY_BYTES 800
#define KYBER512_CIPHERTEXT_BYTES 768
#define KYBER512_BYTES 32

struct pq_kem_st {
  const char *name;
  /* Algorithm-specific public key memory size, in bytes */
  uint16_t public_key_length;
  /* Algorithm-specific private key memory size, in bytes */
  uint16_t private_key_length;
  /* Algorithm-specific ciphertext memory size, in bytes */
  uint16_t ciphertext_length;
  /* Algorithm-specific shared secret memory size, in bytes */
  uint16_t shared_secret_length;

  int (*generate_keypair)(uint8_t *public_key,
                          uint8_t *private_key);
  int (*encapsulate)(uint8_t *ciphertext,
                     uint8_t *shared_secret,
                     const uint8_t *public_key);
  int (*decapsulate)(uint8_t *shared_secret,
                     const uint8_t *cipher_text,
                     const uint8_t *private_key);
};

typedef struct pq_kem_st EVP_PQ_KEM;

OPENSSL_EXPORT extern const EVP_PQ_KEM EVP_PQ_KEM_kyber512;

struct pq_kem_ctx_st {
  const EVP_PQ_KEM *kem;
  uint8_t *public_key;
  uint8_t *private_key;
  uint8_t *ciphertext;
  uint8_t *shared_secret;
};

typedef struct pq_kem_ctx_st EVP_PQ_KEM_CTX;

OPENSSL_EXPORT EVP_PQ_KEM_CTX *EVP_PQ_KEM_CTX_new(void);

OPENSSL_EXPORT int EVP_PQ_KEM_CTX_init(EVP_PQ_KEM_CTX *kem_ctx,
                                       const EVP_PQ_KEM *kem);

OPENSSL_EXPORT void EVP_PQ_KEM_CTX_free(EVP_PQ_KEM_CTX *kem_ctx);

OPENSSL_EXPORT int EVP_PQ_KEM_generate_keypair(EVP_PQ_KEM_CTX *kem_params);

OPENSSL_EXPORT int EVP_PQ_KEM_encapsulate(EVP_PQ_KEM_CTX *kem_params);

OPENSSL_EXPORT int EVP_PQ_KEM_decapsulate(EVP_PQ_KEM_CTX *kem_params);

#endif
