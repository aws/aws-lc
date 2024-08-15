// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "ml_kem.h"
#include "ml_kem_ipd_ref_common/kem.h"
#include "ml_kem_ipd_ref_common/params.h"

#include "./ml_kem_ipd_ref_common/cbd.c"
#include "./ml_kem_ipd_ref_common/indcpa.c"
#include "./ml_kem_ipd_ref_common/kem.c"
#include "./ml_kem_ipd_ref_common/ntt.c"
#include "./ml_kem_ipd_ref_common/poly.c"
#include "./ml_kem_ipd_ref_common/polyvec.c"
#include "./ml_kem_ipd_ref_common/reduce.c"
#include "./ml_kem_ipd_ref_common/symmetric-shake.c"
#include "./ml_kem_ipd_ref_common/verify.c"

// Note: These methods currently default to using the reference code for ML_KEM.
// In a future where AWS-LC has optimized options available, those can be
// conditionally (or based on compile-time flags) called here, depending on
// platform support.

int ml_kem_512_ipd_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                         uint8_t *secret_key  /* OUT */,
                                         const uint8_t *seed  /* IN */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);
  return ml_kem_keypair_derand_ref(&params, public_key, secret_key, seed);
}

int ml_kem_512_ipd_keypair(uint8_t *public_key /* OUT */,
                           uint8_t *secret_key /* OUT */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);
  return ml_kem_keypair_ref(&params, public_key, secret_key);
}

int ml_kem_512_ipd_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed       /* IN */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);
  return ml_kem_enc_derand_ref(&params, ciphertext, shared_secret, public_key, seed);
}

int ml_kem_512_ipd_encapsulate(uint8_t *ciphertext       /* OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               const uint8_t *public_key /* IN  */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);
  return ml_kem_enc_ref(&params, ciphertext, shared_secret, public_key);
}

int ml_kem_512_ipd_decapsulate(uint8_t *shared_secret    /* OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);
  return ml_kem_dec_ref(&params, shared_secret, ciphertext, secret_key);
}

int ml_kem_768_ipd_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                         uint8_t *secret_key  /* OUT */,
                                         const uint8_t *seed  /* IN */) {
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  return ml_kem_keypair_derand_ref(&params, public_key, secret_key, seed);
}

int ml_kem_768_ipd_keypair(uint8_t *public_key /* OUT */,
                           uint8_t *secret_key /* OUT */) {
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  return ml_kem_keypair_ref(&params, public_key, secret_key);
}

int ml_kem_768_ipd_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed       /* IN */) {
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  return ml_kem_enc_derand_ref(&params, ciphertext, shared_secret, public_key, seed);
}

int ml_kem_768_ipd_encapsulate(uint8_t *ciphertext       /* OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               const uint8_t *public_key /* IN  */) {
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  return ml_kem_enc_ref(&params, ciphertext, shared_secret, public_key);
}

int ml_kem_768_ipd_decapsulate(uint8_t *shared_secret    /* OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */) {
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  return ml_kem_dec_ref(&params, shared_secret, ciphertext, secret_key);
}

int ml_kem_1024_ipd_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                          uint8_t *secret_key  /* OUT */,
                                          const uint8_t *seed  /* IN */) {
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  return ml_kem_keypair_derand_ref(&params, public_key, secret_key, seed);
}

int ml_kem_1024_ipd_keypair(uint8_t *public_key /* OUT */,
                            uint8_t *secret_key /* OUT */) {
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  return ml_kem_keypair_ref(&params, public_key, secret_key);
}

int ml_kem_1024_ipd_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                              uint8_t *shared_secret    /* OUT */,
                                              const uint8_t *public_key /* IN  */,
                                              const uint8_t *seed       /* IN */) {
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  return ml_kem_enc_derand_ref(&params, ciphertext, shared_secret, public_key, seed);
}

int ml_kem_1024_ipd_encapsulate(uint8_t *ciphertext       /* OUT */,
                                uint8_t *shared_secret    /* OUT */,
                                const uint8_t *public_key /* IN  */) {
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  return ml_kem_enc_ref(&params, ciphertext, shared_secret, public_key);
}

int ml_kem_1024_ipd_decapsulate(uint8_t *shared_secret    /* OUT */,
                                const uint8_t *ciphertext /* IN  */,
                                const uint8_t *secret_key /* IN  */) {
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  return ml_kem_dec_ref(&params, shared_secret, ciphertext, secret_key);
}
