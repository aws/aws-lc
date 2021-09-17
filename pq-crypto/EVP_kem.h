// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// KEM Library
// Abstract: Post-Quantum Algorithm API
// -----------------------------------------------------------------------------

#ifndef AWSLC_EVP_KEM_H
#define AWSLC_EVP_KEM_H

#include <stdint.h>

// ----------------------------------------------------------------------------
// Name: pq_kem
//
// Description: Keeps track of pq algorithm specific constants
// which are length of public key, private key, cipher text, and shared secret.
// Also contains pointers to the specific algorithms required.
// ----------------------------------------------------------------------------
typedef struct pq_kem {
    // name of pq algorithm specific KEM
    const char *name;
    // stores the pq algorithm specific public key memory size
    const uint16_t public_key_length;
    // stores the pq algorithm specific private key memory size
    const uint16_t private_key_length;
    // stores the pq algorithm specific ciphertext memory size
    const uint16_t ciphertext_length;
    // stores the pq algorithm specific shared secret memory size
    const uint16_t shared_secret_key_length;

    // NIST Post Quantum KEM submissions require the following API for compatibility
    int (*generate_keypair)(unsigned char *public_key, unsigned char *private_key);
    int (*encapsulate)(unsigned char *ciphertext, unsigned char *shared_secret, const unsigned char *public_key);
    int (*decapsulate)(unsigned char *shared_secret, const unsigned char *cipher_text, const unsigned char *private_key);
} pq_kem;



// ----------------------------------------------------------------------------
// Name: pq_kem_params
//
// Description: Keeps track of the actual keys and secrets
// that are pq algorithm specific.
// They are public key, private key, cipher text, and shared secret.
// Also points to the algorithm specific pq_kem struct
// ----------------------------------------------------------------------------
typedef struct pq_kem_params {
    pq_kem *kem;
    unsigned char *public_key;
    unsigned char *private_key;
    unsigned char *ciphertext;
    unsigned char *shared_secret;
} pq_kem_params;

extern const struct pq_kem evp_sike_p434_r3;

// ----------------------------------------------------------------------------
// Name: pq_kem_params_alloc
//
// Arguments: pointer to pq_kem and pq_kem_params.
// pq_kem_params allows access to the lengths and key pointer (output param)
// of public key, private key, cipher text, and shared secret.
//
// Description: Allocates the space needed for public key,
// private key, cipher text, and shared secret.
//
// Return 1 on success, and 0 if it fails.
//  ---------------------------------------------------------------------------
int pq_kem_params_alloc(pq_kem *kem, pq_kem_params *kem_params);

// ----------------------------------------------------------------------------
// Name: pq_kem_params_free
//
// Arguments: pointer to pq_kem_params.
// pq_kem_params allows access to the lengths and key pointer (output param)
// of public key, private key, cipher text, and shared secret.
//
// Description: Frees space of public key, private key, cipher text,
// and shared secret.
//
// Return 1 on success, and 0 if it fails
// ----------------------------------------------------------------------------
int pq_kem_params_free(pq_kem_params *kem_params);

// ----------------------------------------------------------------------------
// Name: EVP_kem_generate_keypair
//
// Description: Generates a public and private key
//
// Arguments: pq_kem_params
// The following fields of pq_kem_params are used for generate keypair:
//  - unsigned char *public_key: pointer to output public key
//  - unsigned char *private_key: pointer to output secret key
//
// Returns 1 on successfully generating key pair,
// returns 0 otherwise and on error
// ----------------------------------------------------------------------------
int EVP_kem_generate_keypair(pq_kem_params *kem_params);

// ----------------------------------------------------------------------------
// Name: EVP_kem_enc
//
// Description: Uses public key to create cipher text and secret key.
//
// Arguments: pq_kem_params
// The following fields of pq_kem_params are used for encapsulate:
//  - unsigned char *cipher_text: pointer to output cipher text
//  - unsigned char *shared_secret: pointer to output shared secret
//  - unsigned char *public_key: pointer to input constant public key
//
// Returns 1 on successful encapsulation, return 0 otherwise and on error
// ----------------------------------------------------------------------------
int EVP_kem_encapsulate(pq_kem_params *kem_params);

// ----------------------------------------------------------------------------
// Name: EVP_kem_dec
//
// Description: Generates shared secret using private key and cipher text
//
// Arguments: pq_kem_params
// The following fields of pq_kem_params are used for decapsulate:
//  - unsigned char *shared_secret: pointer to output shared secret
//  - unsigned char *cipher_text: pointer to input cipher text
//  - unsigned char *private_key: pointer to input constant private key
//
// Returns 1 on successful decapsulation, return 0 otherwise and on error
// ----------------------------------------------------------------------------
int EVP_kem_decapsulate(pq_kem_params *kem_params);

#endif  // AWSLC_EVP_KEM_H
