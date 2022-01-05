#ifndef _PQ_KEM_H_
#define _PQ_KEM_H_

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include "openssl/base.h"

#define KYBER512_SECRET_KEY_BYTES 1632
#define KYBER512_PUBLIC_KEY_BYTES 800
#define KYBER512_CIPHERTEXT_BYTES 768
#define KYBER512_BYTES 32

/*
   Name: pq_kem_st
  
   Description: This defines a PQ KEM algorithm in terms of its attribute values
                and pointers to KEM functions which implement it.
*/
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

  /* This reuses the API definitions used by NIST PQ KEM submissions */
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

/*
   Name: pq_kem_ctx_st
  
   Description: This is a context structure, which holds the algorithm-specific
                keys and secrets, as well as a pointer to the EVP_PQ_KEM
                definition structure.
*/
struct pq_kem_ctx_st {
  const EVP_PQ_KEM *kem;
  uint8_t *public_key;
  uint8_t *private_key;
  uint8_t *ciphertext;
  uint8_t *shared_secret;
};

typedef struct pq_kem_ctx_st EVP_PQ_KEM_CTX;

/*
   Name: EVP_PQ_KEM_CTX_new

   Description: Creates a new EVP_PQ_KEM_CTX.
*/
OPENSSL_EXPORT EVP_PQ_KEM_CTX *EVP_PQ_KEM_CTX_new(void);

/*
   Name: EVP_PQ_KEM_init

   Description: Initializes |kem_ctx| with the given |kem| and allocates memory
                needed for public key, private key, cipher text, and
                shared secret.
  
   Returns 1 on success, 0 on failure.
*/
OPENSSL_EXPORT int EVP_PQ_KEM_CTX_init(EVP_PQ_KEM_CTX *kem_ctx, const EVP_PQ_KEM *kem);

/*
   Name: EVP_PQ_KEM_CTX_free
  
   Arguments: pointer to EVP_PQ_KEM_CTX.
  
   Description: Cleanses and frees the memory of public key, private key,
                cipher text, and shared secret.
*/
OPENSSL_EXPORT void EVP_PQ_KEM_CTX_free(EVP_PQ_KEM_CTX *kem_ctx);

/*
   Name: EVP_PQ_KEM_generate_keypair
  
   Description: Generates a random public and private key.
  
   Returns 1 on success, 0 on failure.
*/
OPENSSL_EXPORT int EVP_PQ_KEM_generate_keypair(EVP_PQ_KEM_CTX *kem_params);

/*
   Name: EVP_PQ_KEM_encapsulate
  
   Description: Generates a random shared secret and encapsulates it using the
                public key to produce the output ciphertext.
  
   Returns 1 on success, 0 on failure.
*/
OPENSSL_EXPORT int EVP_PQ_KEM_encapsulate(EVP_PQ_KEM_CTX *kem_params);

/*
   Name: EVP_PQ_KEM_decapsulate
  
   Description: Decapsulates the ciphertext using the private key to
                output the shared secret.
  
   Returns 1 on success, 0 on failure.
*/
OPENSSL_EXPORT int EVP_PQ_KEM_decapsulate(EVP_PQ_KEM_CTX *kem_params);

#ifdef __cplusplus
}
#endif

#endif
