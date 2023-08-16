// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include "../evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "sig_dilithium.h"
#include "pqcrystals_dilithium_ref_common/api.h"

// Note: These methods currently default to using the reference code for
// Dilithium. In a future where AWS-LC has optimized options available,
// those can be conditionally (or based on compile-time flags) called here,
// depending on platform support.


int DILITHIUM3_keypair(uint8_t *public_key /* OUT */,
                       uint8_t *secret_key /* OUT */) {
  return pqcrystals_dilithium3_ref_keypair(public_key, secret_key);
}

int DILITHIUM3_sign(uint8_t *sig               /* OUT */,
                    size_t *sig_len            /* OUT */,
                    const uint8_t *message     /* IN */,
                    size_t message_len,        /* IN */
                    const uint8_t *secret_key  /* IN */) {
  return pqcrystals_dilithium3_ref_signature(sig, sig_len, message, message_len,
                                             secret_key);
}

int DILITHIUM3_verify(const uint8_t *message    /* IN */,
                      size_t message_len        /* IN */,
                      const uint8_t *sig        /* IN */,
                      size_t sig_len            /* IN */,
                      const uint8_t *public_key /* IN */) {
  return pqcrystals_dilithium3_ref_verify(sig, sig_len, message, message_len,
                                          public_key);
}
