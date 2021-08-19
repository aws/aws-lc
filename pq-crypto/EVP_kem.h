/********************************************************************************************
* KEM Library
*
* Abstract: Post-Quantum Algorithm API
*********************************************************************************************/

#ifndef AWSLC_EVP_KEM_H
#define AWSLC_EVP_KEM_H

#include <stdint.h>
#include "EVP_pq_constants.h"

/*************************************************
* Name: pq_kem
*
* Description: Keeps track of pq algorithm specific
* constants which are length of public key, private key,
* cipher text, and shared secret. Also contains pointers
* to the specific algorithms required.
*
*
**************************************************/

/* typedef to hide the internal details */

typedef struct pq_kem {
    // name of pq algorithm specific KEM
    const char *name;
    // stores the pq algorithm specific public key memory size
    const uint16_t public_key_length;
    // stores the pq algorithm specific private key memory size
    const uint16_t private_key_length;
    // stores the pq algorithm specific shared secret memory size
    const uint16_t shared_secret_key_length;
    // stores the pq algorithm specific ciphertext memory size
    const uint16_t ciphertext_length;

    /* NIST Post Quantum KEM submissions require the following API for compatibility */
    int (*generate_keypair)(OUT unsigned char *public_key, OUT unsigned char *private_key);
    int (*encapsulate)(OUT unsigned char *ciphertext, OUT unsigned char *shared_secret, IN const unsigned char *public_key);
    int (*decapsulate)(OUT unsigned char *shared_secret, IN const unsigned char *cipher_text, IN const unsigned char *private_key);
} pq_kem;

/*************************************************
* Name: pq_kem_params
*
* Description: Keeps track of the actual keys and
* secrets that are pq algorithm specific.
* They are public key, private key,
* cipher text, and shared secret. Also points
* to the algorithm specific pq_kem struct
*
*
**************************************************/

/* typedef to hide the internal details */

typedef struct pq_kem_params {
    pq_kem *kem;
    /*uint32_t *public_key;
    uint32_t *private_key;
    uint32_t *ciphertext;
    uint32_t *shared_secret;*/
    unsigned char *public_key;
    unsigned char *private_key;
    unsigned char *ciphertext;
    unsigned char *shared_secret;
} pq_kem_params;

/*************************************************
* Name: pq_kem_params_alloc
*
* Arguments: pointer to pq_key_params.
* pq_key_params allows access to the lengths and key pointer (output param)
 * of public key, private key, cipher text,
* and shared secret.
* Description: Allocates the space needed for
* public key, private key, cipher text,
* and shared secret.
*
* Return EVP_PQ_SUCCESS on success, and EVP_PQ_FAILURE if it fails.
**************************************************/
int pq_kem_params_alloc(pq_kem_params *key_params);

/*************************************************
* Name: pq_kem_params_free
*
* Arguments: pointer to pq_key_params.
* pq_key_params allows access to the lenghts and key pointer (output param)
 * of public key, private key, cipher text,
* and shared secret.
* Description: Frees space of
* public key, private key, cipher text,
* and shared secret.
*
* Return EVP_PQ_SUCCESS on success, and EVP_PQ_FAILURE if it fails.
**************************************************/
int pq_kem_params_free(pq_kem_params *key_params);

/*************************************************
* Name: EVP_kem_generate_keypair
*
* Description: Generates a public and private key
*
* Arguments: pq_kem_params
* The following fields of pq_kem_params are used for generate keypair:
* - unsigned char *public_key: pointer to output public key
* (already allocated array of bytes)
* - unsigned char *private_key: pointer to output secret key
* (already allocated array of bytes)
*
* Returns EVP_PQ_SUCCESS on successfully generating key pair,
* return EVP_PQ_FAILURE otherwise and on error
**************************************************/
int EVP_kem_generate_keypair(pq_kem_params *kem_params);


/*************************************************
* Name: EVP_kem_enc
*
* Description: Uses public key to create cipher text and secrect key.
*
* Arguments: pq_kem_params
* The following fields of pq_kem_params are used for encapsualte:
* - unsigned char *cipher_text: pointer to output cipher text
* (already allocated array of bytes)
* - unsigned char *shared_secret: pointer to output shared secrect
* (already allocated array of bytes)
* - const unsigned char *public_key: pointer to input constant public key
*
* Returns EVP_PQ_SUCCESS on successful encapsulation,
* return EVP_PQ_FAILURE otherwise and on error
**************************************************/
int EVP_kem_encapsulate(pq_kem_params *kem_params);


/*************************************************
* Name: EVP_kem_dec
*
* Description: Generates shared secret for public key and cipher text
*
* Arguments: pq_kem_params
* The following fields of pq_kem_params are used for decapsulate:
* - unsigned char *shared_secret: pointer to output shared secret
* (already allocated array of bytes)
* - unsigned char *cipher_text: pointer to input cipher text
* (already allocated array of bytes)
* - const unsigned char *private_key: pointer to input constant private key
*
* Returns EVP_PQ_SUCCESS on successful decapsulation,
* return EVP_PQ_FAILURE otherwise and on error
**************************************************/
int EVP_kem_decapsulate(pq_kem_params *kem_params);


/* SIKE's key generation
 * Outputs: private key (SIKE_P434_R3_SECRET_KEY_BYTES = SIKE_P434_R3_MSG_BYTES + SIKE_P434_R3_SECRETKEY_B_BYTES + SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
 *          public key (SIKE_P434_R3_PUBLIC_KEY_BYTES bytes) */
int evp_sike_p434_r3_crypto_kem_keypair(OUT unsigned char *public_key, OUT unsigned char *private_key);

/* SIKE's encapsulation
 * Input:   public key         (SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
 * Outputs: shared secret      (SIKE_P434_R3_SHARED_SECRET_BYTES bytes)
 *          ciphertext message (SIKE_P434_R3_CIPHERTEXT_BYTES = SIKE_P434_R3_PUBLIC_KEY_BYTES + SIKE_P434_R3_MSG_BYTES bytes) */
int evp_sike_p434_r3_crypto_kem_enc(OUT unsigned char *ciphertext, OUT unsigned char *shared_secret, IN const unsigned char *public_key);


/* SIKE's decapsulation
 * Input:   private_key         (SIKE_P434_R3_SECRET_KEY_BYTES = SIKE_P434_R3_MSG_BYTES + SIKE_P434_R3_SECRETKEY_B_BYTES + SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
 *          ciphertext message  (SIKE_P434_R3_CIPHERTEXT_BYTES = SIKE_P434_R3_PUBLIC_KEY_BYTES + SIKE_P434_R3_MSG_BYTES bytes)
 * Outputs: shared secret ss    (SIKE_P434_R3_SHARED_SECRET_BYTES bytes) */
int evp_sike_p434_r3_crypto_kem_dec(OUT unsigned char *shared_secret, IN const unsigned char *ciphertext, IN const unsigned char *private_key);

/* SIKE's private constant time copy function.
 * Current work around for not being able to find a aws-lc
 * version of constant time copy function. */
int sike_copy_or_dont(uint8_t * dest, const uint8_t * src, uint32_t len, bool dont);

#endif  // AWSLC_EVP_KEM_H
