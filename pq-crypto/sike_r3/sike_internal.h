// -----------------------------------------------------------------------------
// Supersingular Isogeny Key Encapsulation Library
//
// Abstract: supersingular isogeny key encapsulation (SIKE) protocol
// NOTE: Currently the use of constant time functions to copy and compare has been
// replaced with memcpy and memcmp as a work around.
// -----------------------------------------------------------------------------

#ifndef PQ_CRYPTO_SIKE_INTERNAL_H
#define PQ_CRYPTO_SIKE_INTERNAL_H

// SIKEP434 Round 3 PQ Algorithm Constants
#define SIKE_P434_R3_PUBLIC_KEY_BYTES 330
#define SIKE_P434_R3_PRIVATE_KEY_BYTES 374
#define SIKE_P434_R3_CIPHERTEXT_BYTES 346
#define SIKE_P434_R3_SHARED_SECRET_BYTES 16

// -----------------------------------------------------------------------------
// SIKE's key generation
// Outputs: private key (SIKE_P434_R3_SECRET_KEY_BYTES = SIKE_P434_R3_MSG_BYTES +
//          SIKE_P434_R3_SECRETKEY_B_BYTES + SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
//          public key (SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
// -----------------------------------------------------------------------------
int sike_p434_r3_crypto_kem_keypair(unsigned char *public_key, unsigned char *private_key);

// -----------------------------------------------------------------------------
// SIKE's encapsulation
// Input:   public key         (SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
// Outputs: shared secret      (SIKE_P434_R3_SHARED_SECRET_BYTES bytes)
//          ciphertext message (SIKE_P434_R3_CIPHERTEXT_BYTES = SIKE_P434_R3_PUBLIC_KEY_BYTES
//          + SIKE_P434_R3_MSG_BYTES bytes)
// -----------------------------------------------------------------------------
int sike_p434_r3_crypto_kem_enc(unsigned char *ciphertext, unsigned char *shared_secret, const unsigned char *public_key);

// -----------------------------------------------------------------------------
// SIKE's decapsulation
// Input:   private_key         (SIKE_P434_R3_SECRET_KEY_BYTES = SIKE_P434_R3_MSG_BYTES +
//                              SIKE_P434_R3_SECRETKEY_B_BYTES + SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
//          ciphertext message  (SIKE_P434_R3_CIPHERTEXT_BYTES = SIKE_P434_R3_PUBLIC_KEY_BYTES +
//                              SIKE_P434_R3_MSG_BYTES bytes)
// Outputs: shared secret ss    (SIKE_P434_R3_SHARED_SECRET_BYTES bytes)
// -----------------------------------------------------------------------------
int sike_p434_r3_crypto_kem_dec(unsigned char *shared_secret, const unsigned char *ciphertext, const unsigned char *private_key);


#endif //PQ_CRYPTO_SIKE_INTERNAL_H
