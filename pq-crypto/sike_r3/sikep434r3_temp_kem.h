//
// Created by lamjyoti on 8/9/2021.
//

#ifndef SIKEP434R3_CONSTANTS_H
#define SIKEP434R3_CONSTANTS_H

/* TLDR s2n: 0=true, -1=false,
 * TLDR aws-lc: 1=true, 0=false
 * current work around to keep following macros */
#define S2N_SUCCESS 1
#define S2N_FAILURE 0


/* SIKE PQ Algorithm Constants */
#define SIKE_P434_R3_PUBLIC_KEY_BYTES 330
#define SIKE_P434_R3_SECRET_KEY_BYTES 374
#define SIKE_P434_R3_CIPHERTEXT_BYTES 346
#define SIKE_P434_R3_SHARED_SECRET_BYTES 16


// Proposed TEMP work around for POSIX_GUARD and POSIX_GUARD_RESULT:
// Currently simplify to only two macros 1 (pass) and 0 (fail)
#define POSIX_GUARD(result) __S2N_ENSURE((result) == S2N_SUCCESS, return S2N_FAILURE)

/**
 * REMOVE LATER
 * Ensures `cond` is true, otherwise `action` will be performed
 */
#define __S2N_ENSURE( cond, action ) do {if ( !(cond) ) { action; }} while (0)


/* SIKE kem functions:
 * key generation
 * key encapsualte
 * key decapsulate
 * */

/* SIKE's key generation
 * Outputs: secret key sk (S2N_SIKE_P434_R3_SECRET_KEY_BYTES = S2N_SIKE_P434_R3_MSG_BYTES + S2N_SIKE_P434_R3_SECRETKEY_B_BYTES + S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
 *          public key pk (S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES bytes) */
int s2n_sike_p434_r3_crypto_kem_keypair(unsigned char *pk, unsigned char *sk);


/* SIKE's encapsulation
 * Input:   public key pk         (S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
 * Outputs: shared secret ss      (S2N_SIKE_P434_R3_SHARED_SECRET_BYTES bytes)
 *          ciphertext message ct (S2N_SIKE_P434_R3_CIPHERTEXT_BYTES = S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES + S2N_SIKE_P434_R3_MSG_BYTES bytes) */
int s2n_sike_p434_r3_crypto_kem_enc(unsigned char *ct, unsigned char *ss, const unsigned char *pk);



/* SIKE's decapsulation
 * Input:   secret key sk         (S2N_SIKE_P434_R3_SECRET_KEY_BYTES = S2N_SIKE_P434_R3_MSG_BYTES + S2N_SIKE_P434_R3_SECRETKEY_B_BYTES + S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
 *          ciphertext message ct (S2N_SIKE_P434_R3_CIPHERTEXT_BYTES = S2N_SIKE_P434_R3_PUBLIC_KEY_BYTES + S2N_SIKE_P434_R3_MSG_BYTES bytes)
 * Outputs: shared secret ss      (S2N_SIKE_P434_R3_SHARED_SECRET_BYTES bytes) */
int s2n_sike_p434_r3_crypto_kem_dec(unsigned char *ss, const unsigned char *ct, const unsigned char *sk);


/* SIKE's private constant time copy function.
 * Current work around for not being able to find a aws-lc
 * version of constant time copy function. */
int constant_time_copy_or_dont(uint8_t * dest, const uint8_t * src, uint32_t len, uint8_t dont);

#endif  // SIKEP434R3_CONSTANTS_H
