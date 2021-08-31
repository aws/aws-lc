// -----------------------------------------------------------------------------
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Supersingular Isogeny Key Encapsulation Library
//
// Abstract: supersingular isogeny key encapsulation (SIKE) protocol
// NOTE: Currently the use of constant time functions to copy and compare has been
// replaced with memcpy and memcmp as a work around.
// -----------------------------------------------------------------------------

#include <string.h>
#include "sikep434r3.h"
#include "sikep434r3_fips202.h"
#include "../../crypto/internal.h"
#include "sike_internal.h"
#include "../../include/openssl/rand.h"
#include "sikep434r3_api.h"


// SIKE's decapsulation helper method
// Copy src to dst, or don't copy it, in constant time
int constant_time_copy_or_dont(uint8_t * dest, const uint8_t * src, uint32_t len, uint8_t dont);

// SIKE's key generation
// Note: secret key is private key
// Outputs: secret key sk (SIKE_P434_R3_SECRET_KEY_BYTES = SIKE_P434_R3_MSG_BYTES + SIKE_P434_R3_SECRETKEY_B_BYTES + SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
//          public key pk (SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
int sike_p434_r3_crypto_kem_keypair(unsigned char *pk, unsigned char *sk)
{
    // Generate lower portion of secret key sk <- s||SK
    RAND_bytes(sk, SIKE_P434_R3_MSG_BYTES);
    random_mod_order_B(sk + SIKE_P434_R3_MSG_BYTES);

    // Generate public key pk
    EphemeralKeyGeneration_B(sk + SIKE_P434_R3_MSG_BYTES, pk);

    // Append public key pk to secret key sk
    memcpy(&sk[SIKE_P434_R3_MSG_BYTES + SIKE_P434_R3_SECRETKEY_B_BYTES], pk, SIKE_P434_R3_PUBLIC_KEY_BYTES);

    return 1;
}

// SIKE's encapsulation
// Input:   public key pk         (SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
// Outputs: shared secret ss      (SIKE_P434_R3_SHARED_SECRET_BYTES bytes)
//          ciphertext message ct (SIKE_P434_R3_CIPHERTEXT_BYTES = SIKE_P434_R3_PUBLIC_KEY_BYTES + SIKE_P434_R3_MSG_BYTES bytes)
int sike_p434_r3_crypto_kem_enc(unsigned char *ct, unsigned char *ss, const unsigned char *pk)
{
    unsigned char ephemeralsk[SIKE_P434_R3_SECRETKEY_A_BYTES];
    unsigned char jinvariant[SIKE_P434_R3_FP2_ENCODED_BYTES];
    unsigned char h[SIKE_P434_R3_MSG_BYTES];
    unsigned char temp[SIKE_P434_R3_CIPHERTEXT_BYTES+SIKE_P434_R3_MSG_BYTES];

    // Generate ephemeralsk <- G(m||pk) mod oA
    RAND_bytes(temp, SIKE_P434_R3_MSG_BYTES) != 1);
    memcpy(&temp[SIKE_P434_R3_MSG_BYTES], pk, SIKE_P434_R3_PUBLIC_KEY_BYTES);
    shake256(ephemeralsk, SIKE_P434_R3_SECRETKEY_A_BYTES, temp, SIKE_P434_R3_PUBLIC_KEY_BYTES+SIKE_P434_R3_MSG_BYTES);
    ephemeralsk[SIKE_P434_R3_SECRETKEY_A_BYTES - 1] &= SIKE_P434_R3_MASK_ALICE;

    // Encrypt
    EphemeralKeyGeneration_A(ephemeralsk, ct);
    EphemeralSecretAgreement_A(ephemeralsk, pk, jinvariant);
    shake256(h, SIKE_P434_R3_MSG_BYTES, jinvariant, SIKE_P434_R3_FP2_ENCODED_BYTES);
    for (int i = 0; i < SIKE_P434_R3_MSG_BYTES; i++) {
        ct[i + SIKE_P434_R3_PUBLIC_KEY_BYTES] = temp[i] ^ h[i];
    }

    // Generate shared secret ss <- H(m||ct)
    memcpy(&temp[SIKE_P434_R3_MSG_BYTES], ct, SIKE_P434_R3_CIPHERTEXT_BYTES);
    shake256(ss, SIKE_P434_R3_SHARED_SECRET_BYTES, temp, SIKE_P434_R3_CIPHERTEXT_BYTES+SIKE_P434_R3_MSG_BYTES);

    return 1;
}

// SIKE's decapsulation
// Input:   secret key sk         (SIKE_P434_R3_SECRET_KEY_BYTES = SIKE_P434_R3_MSG_BYTES + SIKE_P434_R3_SECRETKEY_B_BYTES + SIKE_P434_R3_PUBLIC_KEY_BYTES bytes)
//          ciphertext message ct (SIKE_P434_R3_CIPHERTEXT_BYTES = SIKE_P434_R3_PUBLIC_KEY_BYTES + SIKE_P434_R3_MSG_BYTES bytes)
// Outputs: shared secret ss      (SIKE_P434_R3_SHARED_SECRET_BYTES bytes)
int sike_p434_r3_crypto_kem_dec(unsigned char *ss, const unsigned char *ct, const unsigned char *sk)
{
    unsigned char ephemeralsk_[SIKE_P434_R3_SECRETKEY_A_BYTES];
    unsigned char jinvariant_[SIKE_P434_R3_FP2_ENCODED_BYTES];
    unsigned char h_[SIKE_P434_R3_MSG_BYTES];
    unsigned char c0_[SIKE_P434_R3_PUBLIC_KEY_BYTES];
    unsigned char temp[SIKE_P434_R3_CIPHERTEXT_BYTES+SIKE_P434_R3_MSG_BYTES];

    // Decrypt
    EphemeralSecretAgreement_B(sk + SIKE_P434_R3_MSG_BYTES, ct, jinvariant_);
    shake256(h_, SIKE_P434_R3_MSG_BYTES, jinvariant_, SIKE_P434_R3_FP2_ENCODED_BYTES);
    for (int i = 0; i < SIKE_P434_R3_MSG_BYTES; i++) {
        temp[i] = ct[i + SIKE_P434_R3_PUBLIC_KEY_BYTES] ^ h_[i];
    }

    // Generate ephemeralsk_ <- G(m||pk) mod oA
    memcpy(&temp[SIKE_P434_R3_MSG_BYTES], &sk[SIKE_P434_R3_MSG_BYTES + SIKE_P434_R3_SECRETKEY_B_BYTES], SIKE_P434_R3_PUBLIC_KEY_BYTES);
    shake256(ephemeralsk_, SIKE_P434_R3_SECRETKEY_A_BYTES, temp, SIKE_P434_R3_PUBLIC_KEY_BYTES+SIKE_P434_R3_MSG_BYTES);
    ephemeralsk_[SIKE_P434_R3_SECRETKEY_A_BYTES - 1] &= SIKE_P434_R3_MASK_ALICE;

    // Generate shared secret ss <- H(m||ct), or output ss <- H(s||ct) in case of ct verification failure
    EphemeralKeyGeneration_A(ephemeralsk_, c0_);

    // Verify ciphertext.
    // If c0_ and ct are NOT equal, decaps failed and we overwrite the shared secret
    // with pseudorandom noise (ss = H(s||ct)) by performing the copy (dont_copy = false).
    //
    // If c0_ and ct are equal, then decaps succeeded and we skip the overwrite and output
    // the actual shared secret: ss = H(m||ct) (dont_copy = true).
    int dont_copy = !(CRYPTO_memcmp(c0_, ct, SIKE_P434_R3_PUBLIC_KEY_BYTES));
    constant_time_copy_or_dont(temp, sk, SIKE_P434_R3_MSG_BYTES, dont_copy);

    memcpy(&temp[SIKE_P434_R3_MSG_BYTES], ct, SIKE_P434_R3_CIPHERTEXT_BYTES);
    shake256(ss, SIKE_P434_R3_SHARED_SECRET_BYTES, temp, SIKE_P434_R3_CIPHERTEXT_BYTES+SIKE_P434_R3_MSG_BYTES);

    return 1;
}

// SIKE's decapsulation helper method
// Given arrays "dest" and "src" of length "len", conditionally copy "src" to "dest"
// The execution time of this function is independent of the values
// stored in the arrays, and of whether the copy occurs.
//
// Timing may depend on the length of the arrays, and on the location
// of the arrays in memory (e.g. if a buffer has been paged out, this
// will affect the timing of this function).
int constant_time_copy_or_dont(uint8_t * dest, const uint8_t * src, uint32_t len, uint8_t dont)
{
    uint8_t mask = (((0xFFFF & dont) - 1) >> 8) & 0xFF;

    // dont = 0 : mask = 0xff
    // dont > 0 : mask = 0x00

    for (uint32_t i = 0; i < len; i++) {
        uint8_t old = dest[i];
        uint8_t diff = (old ^ src[i]) & mask;
        dest[i] = old ^ diff;
    }

    return 1;
}
