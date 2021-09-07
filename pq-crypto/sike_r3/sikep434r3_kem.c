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
#include "sikep434r3_fpx.h"


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
    RAND_bytes(temp, SIKE_P434_R3_MSG_BYTES);
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
    // If selector = 0 then do ss = H(m||ct), else if selector = -1 load s to do ss = H(s||ct)
    int8_t selector = ct_compare(c0_, ct, SIKE_P434_R3_PUBLIC_KEY_BYTES);
    ct_cmov(temp, sk, SIKE_P434_R3_MSG_BYTES, selector);

    memcpy(&temp[SIKE_P434_R3_MSG_BYTES], ct, SIKE_P434_R3_CIPHERTEXT_BYTES);
    shake256(ss, SIKE_P434_R3_SHARED_SECRET_BYTES, temp, SIKE_P434_R3_CIPHERTEXT_BYTES+SIKE_P434_R3_MSG_BYTES);

    return 1;
}
