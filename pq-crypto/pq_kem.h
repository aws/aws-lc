// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// KEM Library
// Abstract: Post-Quantum Algorithm API
// -----------------------------------------------------------------------------
#ifdef __cplusplus
extern "C" {
#endif

#ifndef AWSLC_EVP_KEM_H
#define AWSLC_EVP_KEM_H

#include <stdint.h>
#include "openssl/base.h"

// ----------------------------------------------------------------------------
// Name: pq_kem_st
//
// Description: Keeps track of pq algorithm specific constants
// which are length of public key, private key, cipher text, and shared secret.
// Also contains pointers to the specific algorithms required.
// ----------------------------------------------------------------------------
struct pq_kem_st {
  // Name of PQ algorithm specific KEM.
  const char *name;
  // Stores the pq algorithm specific public key memory size.
  uint16_t public_key_length;
  // Stores the pq algorithm specific private key memory size.
  uint16_t private_key_length;
  // Stores the pq algorithm specific ciphertext memory size.
  uint16_t ciphertext_length;
  // Stores the pq algorithm specific shared secret memory size.
  uint16_t shared_secret_length;

  // NIST PQ KEM submissions require the following API for compatibility.
  int (*generate_keypair)(unsigned char *public_key,
                          unsigned char *private_key);
  int (*encapsulate)(unsigned char *ciphertext,
                     unsigned char *shared_secret,
                     const unsigned char *public_key);
  int (*decapsulate)(unsigned char *shared_secret,
                     const unsigned char *cipher_text,
                     const unsigned char *private_key);
};

typedef struct pq_kem_st EVP_PQ_KEM;

OPENSSL_EXPORT extern const EVP_PQ_KEM EVP_PQ_KEM_sike_p434_r3;

// ----------------------------------------------------------------------------
// Name: pq_kem_ctx_st
//
// Description: Keeps track of the actual keys and secrets
// that are PQ algorithm specific.
// They are public key, private key, cipher text, and shared secret.
// Also points to the algorithm specific EVP_PQ_KEM struct.
// ----------------------------------------------------------------------------
struct pq_kem_ctx_st {
  const EVP_PQ_KEM *kem;
  unsigned char *public_key;
  unsigned char *private_key;
  unsigned char *ciphertext;
  unsigned char *shared_secret;
};

typedef struct pq_kem_ctx_st EVP_PQ_KEM_CTX;

// ----------------------------------------------------------------------------
// Name: EVP_PQ_KEM_CTX_new
//
// Description: Creates a new EVP_PQ_KEM_CTX.
//
//  ---------------------------------------------------------------------------
OPENSSL_EXPORT EVP_PQ_KEM_CTX *EVP_PQ_KEM_CTX_new(void);

// ----------------------------------------------------------------------------
// Name: EVP_PQ_KEM_init
//
// Description: Initializes |kem_ctx| with the given |kem| and allocates memory
// needed for public key, private key, cipher text, and shared secret.
//
// Returns 1 on success, and 0 if it fails.
//  ---------------------------------------------------------------------------
OPENSSL_EXPORT int EVP_PQ_KEM_CTX_init(EVP_PQ_KEM_CTX *kem_ctx,
                                       const EVP_PQ_KEM *kem);

// ----------------------------------------------------------------------------
// Name: EVP_PQ_KEM_CTX_free
//
// Arguments: pointer to EVP_PQ_KEM_CTX.
//
// Description: Zeroizes and frees the memory of public key, private key,
// cipher text, and shared secret.
// ----------------------------------------------------------------------------
OPENSSL_EXPORT void EVP_PQ_KEM_CTX_free(EVP_PQ_KEM_CTX *kem_ctx);

// ----------------------------------------------------------------------------
// Name: EVP_PQ_KEM_generate_keypair
//
// Description: Generates a random public and private key.
//
// Returns 1 on successfully generating key pair,
// returns 0 otherwise and on error.
// ----------------------------------------------------------------------------
OPENSSL_EXPORT int EVP_PQ_KEM_generate_keypair(EVP_PQ_KEM_CTX *kem_params);

// ----------------------------------------------------------------------------
// Name: EVP_PQ_KEM_encapsulate
//
// Description: PQ KEM encapsulation -- generates a random shared secret and
// using the public key encapsulates it to the output ciphertext.
//
// Returns 1 on successful encapsulation, return 0 otherwise and on error.
// ----------------------------------------------------------------------------
OPENSSL_EXPORT int EVP_PQ_KEM_encapsulate(EVP_PQ_KEM_CTX *kem_params);

// ----------------------------------------------------------------------------
// Name: EVP_PQ_KEM_decapsulate
//
// Description: PQ KEM decapsulation -- using the private key decapsulates
// the ciphertext to the output shared secret.
//
// Returns 1 on successful decapsulation, return 0 otherwise and on error.
// ----------------------------------------------------------------------------
OPENSSL_EXPORT int EVP_PQ_KEM_decapsulate(EVP_PQ_KEM_CTX *kem_params);

#endif  // AWSLC_EVP_KEM_H

#ifdef __cplusplus
}
#endif
