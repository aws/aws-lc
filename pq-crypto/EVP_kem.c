// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// KEM Library
// Abstract: Post-Quantum Algorithm API
// -----------------------------------------------------------------------------

#include <stdint.h>
#include <stdlib.h>
#include "EVP_kem.h"
#include "sike_r3/sike_internal.h"
#include "../include/openssl/mem.h"

const struct pq_kem evp_sike_p434_r3 = {
        .name = "SIKEp434r3-KEM",
        .public_key_length = SIKE_P434_R3_PUBLIC_KEY_BYTES,
        .private_key_length = SIKE_P434_R3_PRIVATE_KEY_BYTES,
        .shared_secret_key_length = SIKE_P434_R3_SHARED_SECRET_BYTES,
        .ciphertext_length = SIKE_P434_R3_CIPHERTEXT_BYTES,
        .generate_keypair = &sike_p434_r3_crypto_kem_keypair,
        .encapsulate = &sike_p434_r3_crypto_kem_enc,
        .decapsulate = &sike_p434_r3_crypto_kem_dec,
};

int pq_kem_params_alloc(pq_kem *kem, pq_kem_params *kem_params) {
    kem_params->kem = kem;
    kem_params->public_key = OPENSSL_malloc(kem_params->kem->public_key_length);
    if (kem_params->public_key == NULL) {
        return 0;
    }
    kem_params->private_key = OPENSSL_malloc(kem_params->kem->private_key_length);
    if (kem_params->private_key == NULL) {
        return 0;
    }
    kem_params->ciphertext = OPENSSL_malloc(kem_params->kem->ciphertext_length);
    if (kem_params->ciphertext == NULL) {
        return 0;
    }
    kem_params->shared_secret = OPENSSL_malloc(kem_params->kem->shared_secret_key_length);
    if (kem_params->shared_secret == NULL) {
        return 0;
    }

    return 1;
}

int pq_kem_params_free(pq_kem_params *kem_params) {
    if (kem_params != NULL) {
        OPENSSL_free(kem_params->public_key);
        OPENSSL_free(kem_params->private_key);
        OPENSSL_free(kem_params->ciphertext);
        OPENSSL_free(kem_params->shared_secret);
    }

    return 1;
}

int EVP_kem_generate_keypair(pq_kem_params *kem_params) {

    if (kem_params == NULL || kem_params->kem == NULL) {
        return 0;
    }
    pq_kem *kem = kem_params->kem;
    if (kem->generate_keypair == NULL ||
        kem_params->public_key == NULL ||
        kem_params->private_key == NULL) {
        return 0;
    }
    return kem->generate_keypair(kem_params->public_key, kem_params->private_key);
}

int EVP_kem_encapsulate(pq_kem_params *kem_params) {

    if (kem_params == NULL || kem_params->kem == NULL) {
        return 0;
    }
    pq_kem *kem = kem_params->kem;
    if (kem->encapsulate == NULL ||
        kem_params->public_key == NULL ||
        kem_params->ciphertext == NULL) {
        return 0;
    }
    return kem->encapsulate(kem_params->ciphertext, kem_params->shared_secret, kem_params->public_key);
}

int EVP_kem_decapsulate(pq_kem_params *kem_params) {

    if (kem_params == NULL || kem_params->kem == NULL) {
        return 0;
    }
    pq_kem *kem = kem_params->kem;
    if (kem->decapsulate == NULL ||
        kem_params->private_key == NULL ||
        kem_params->ciphertext == NULL) {
        return 0;
    }
    return kem->decapsulate(kem_params->shared_secret, kem_params->ciphertext, kem_params->private_key);
}
