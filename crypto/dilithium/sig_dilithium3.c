// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include "../evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "sig_dilithium.h"
#include "pqcrystals-dilithium_dilithium3_ref/api.h"

// Note: These methods currently default to using the reference code for
// Dilithium. In a future where AWS-LC has optimized options available,
// those can be conditionally (or based on compile-time flags) called here,
// depending on platform support.

int pqcrystals_dilithium3_ref_keypair(uint8_t *pk, uint8_t *sk);
int pqcrystals_dilithium3_ref_signature(uint8_t *sig, size_t *siglen,
                                        const uint8_t *m, size_t mlen,
                                        const uint8_t *sk);
int pqcrystals_dilithium3_ref_verify(const uint8_t *sig, size_t siglen,
                                     const uint8_t *m, size_t mlen,
                                     const uint8_t *pk);

int DILITHIUM3_keypair(uint8_t *public_key,
                       uint8_t *secret_key) {
  return pqcrystals_dilithium3_ref_keypair(public_key, secret_key);
}

int DILITHIUM3_sign(uint8_t *sig,
                    size_t *sig_len,
                    const uint8_t *message,
                    size_t message_len,
                    const uint8_t *secret_key) {
  return pqcrystals_dilithium3_ref_signature(sig, sig_len, message, message_len,
                                             secret_key);
}

int DILITHIUM3_verify(const uint8_t *message,
                      size_t message_len,
                      const uint8_t *sig,
                      size_t sig_len,
                      const uint8_t *public_key) {
  return pqcrystals_dilithium3_ref_verify(sig, sig_len, message, message_len,
                                          public_key);
}
