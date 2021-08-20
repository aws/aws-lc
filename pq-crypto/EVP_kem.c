/********************************************************************************************
* KEM Library
*
* Abstract: Post-Quantum Algorithm API
*********************************************************************************************/

#include <stdint.h>
#include <stdlib.h>
#include "EVP_kem.h"
#include "EVP_pq_constants.h"

struct pq_kem evp_sike_p434_r3 = {
        .name = "SIKEp434r3-KEM",
        .public_key_length = SIKE_P434_R3_PUBLIC_KEY_BYTES,
        .private_key_length = SIKE_P434_R3_PRIVATE_KEY_BYTES,
        .shared_secret_key_length = SIKE_P434_R3_SHARED_SECRET_BYTES,
        .ciphertext_length = SIKE_P434_R3_CIPHERTEXT_BYTES,
        .generate_keypair = &evp_sike_p434_r3_crypto_kem_keypair,
        .encapsulate = &evp_sike_p434_r3_crypto_kem_enc,
        .decapsulate = &evp_sike_p434_r3_crypto_kem_dec,
};

const struct pq_kem_params evp_sike_kem_params = {
    .kem = &evp_sike_p434_r3,
    .public_key = NULL,
    .public_key_size = 0,
    .private_key = NULL,
    .private_key_size = 0,
    .ciphertext = NULL,
    .ciphertext_size = 0,
    .shared_secret = NULL,
    .shared_secret_size = 0,
};

int pq_kem_params_alloc(pq_kem_params *key_params) {
    key_params->public_key = malloc(key_params->kem->public_key_length);
    key_params->public_key_size = key_params->kem->public_key_length;
    key_params->private_key = malloc(key_params->kem->private_key_length);
    key_params->private_key_size = key_params->kem->private_key_length;
    key_params->ciphertext = malloc(key_params->kem->ciphertext_length);
    key_params->ciphertext_size = key_params->kem->ciphertext_length;
    key_params->shared_secret = malloc(key_params->kem->shared_secret_key_length);
    key_params->shared_secret_size = key_params->kem->shared_secret_key_length;

    return EVP_PQ_SUCCESS;
}

int pq_kem_params_free(pq_kem_params *key_params) {
    if (key_params != NULL) {
        free(key_params->public_key);
        free(key_params->private_key);
        free(key_params->ciphertext);
        free(key_params->shared_secret);
        return EVP_PQ_SUCCESS;
    }
    return EVP_PQ_SUCCESS;
}

int EVP_kem_generate_keypair(pq_kem_params *kem_params) {

    // check for empty references
    if (kem_params == NULL || kem_params->kem == NULL) {
        return EVP_PQ_FAILURE;
    }
    pq_kem *kem = kem_params->kem;
    if (kem->generate_keypair == NULL) {
        return EVP_PQ_FAILURE;
    }

    // check public key
    if (kem_params->public_key == NULL || kem_params->public_key_size != kem->public_key_length) {
        return EVP_PQ_FAILURE;
    }
    //  check private key
    if (kem_params->private_key == NULL || kem_params->private_key_size != kem->private_key_length) {
        return EVP_PQ_FAILURE;
    }

    int result = kem->generate_keypair(kem_params->public_key, kem_params->private_key);
    return result;
}

// should the ciphertext be sent here and then saved in the kem??
int EVP_kem_encapsulate(pq_kem_params *kem_params) {

    // check for empty references
    if (kem_params == NULL || kem_params->kem == NULL) {
        return EVP_PQ_FAILURE;
    }
    pq_kem *kem = kem_params->kem;
    if (kem->encapsulate == NULL) {
        return EVP_PQ_FAILURE;
    }

    // check public key
    if (kem_params->public_key == NULL || kem_params->public_key_size != kem->public_key_length) {
        return EVP_PQ_FAILURE;
    }
    // check ciphertext
    if (kem_params->ciphertext == NULL || kem_params->ciphertext_size != kem->ciphertext_length) {
        return EVP_PQ_FAILURE;
    }

    int result = kem->encapsulate(kem_params->ciphertext, kem_params->shared_secret, kem_params->public_key);
    return result;
}

int EVP_kem_decapsulate(pq_kem_params *kem_params) {

    // check for empty references
    if (kem_params == NULL || kem_params->kem == NULL) {
        return EVP_PQ_FAILURE;
    }
    pq_kem *kem = kem_params->kem;
    if (kem->decapsulate == NULL) {
        return EVP_PQ_FAILURE;
    }

    // check public key
    if (kem_params->private_key == NULL || kem_params->private_key_size != kem->private_key_length) {
        return EVP_PQ_FAILURE;
    }
    // check ciphertext
    if (kem_params->ciphertext == NULL || kem_params->ciphertext_size != kem->ciphertext_length) {
        return EVP_PQ_FAILURE;
    }

    int result = kem->decapsulate(kem_params->shared_secret, kem_params->ciphertext, kem_params->private_key);
    return result;
}
