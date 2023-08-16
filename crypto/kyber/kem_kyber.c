// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "../evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "kem_kyber.h"
#include "pqcrystals_kyber_ref_common/api.h"

// Note: These methods currently default to using the reference code for Kyber.
// In a future where AWS-LC has optimized options available, those can be
// conditionally (or based on compile-time flags) called here, depending on
// platform support.

int kyber512r3_keypair(uint8_t *public_key /* OUT */,
                       uint8_t *secret_key /* OUT */) {
  return pqcrystals_kyber512_ref_keypair(public_key, secret_key);
}

int kyber512r3_encapsulate(uint8_t *ciphertext       /* OUT */,
                           uint8_t *shared_secret    /* OUT */,
                           const uint8_t *public_key /* IN  */) {
  return pqcrystals_kyber512_ref_enc(ciphertext, shared_secret, public_key);
}

int kyber512r3_decapsulate(uint8_t *shared_secret    /* OUT */,
                           const uint8_t *ciphertext /* IN  */,
                           const uint8_t *secret_key /* IN  */) {
  return pqcrystals_kyber512_ref_dec(shared_secret, ciphertext, secret_key);
}

int kyber768r3_keypair(uint8_t *public_key /* OUT */,
                       uint8_t *secret_key /* OUT */) {
  return pqcrystals_kyber768_ref_keypair(public_key, secret_key);
}

int kyber768r3_encapsulate(uint8_t *ciphertext       /* OUT */,
                           uint8_t *shared_secret    /* OUT */,
                           const uint8_t *public_key /* IN  */) {
  return pqcrystals_kyber768_ref_enc(ciphertext, shared_secret, public_key);
}

int kyber768r3_decapsulate(uint8_t *shared_secret    /* OUT */,
                           const uint8_t *ciphertext /* IN  */,
                           const uint8_t *secret_key /* IN  */) {
  return pqcrystals_kyber768_ref_dec(shared_secret, ciphertext, secret_key);
}

int kyber1024r3_keypair(uint8_t *public_key /* OUT */,
                        uint8_t *secret_key /* OUT */) {
  return pqcrystals_kyber1024_ref_keypair(public_key, secret_key);
}

int kyber1024r3_encapsulate(uint8_t *ciphertext       /* OUT */,
                            uint8_t *shared_secret    /* OUT */,
                            const uint8_t *public_key /* IN  */) {
  return pqcrystals_kyber1024_ref_enc(ciphertext, shared_secret, public_key);
}

int kyber1024r3_decapsulate(uint8_t *shared_secret    /* OUT */,
                            const uint8_t *ciphertext /* IN  */,
                            const uint8_t *secret_key /* IN  */) {
  return pqcrystals_kyber1024_ref_dec(shared_secret, ciphertext, secret_key);
}
