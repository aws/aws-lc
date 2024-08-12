// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "ml_kem.h"
#include "ml_kem_ipd_ref_common/api.h"
#include "ml_kem_ipd_ref_common/params.h"

// Note: These methods currently default to using the reference code for ML_KEM.
// In a future where AWS-LC has optimized options available, those can be
// conditionally (or based on compile-time flags) called here, depending on
// platform support.

int ml_kem_512_ipd_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                         uint8_t *secret_key  /* OUT */,
                                         const uint8_t *seed  /* IN */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);
  return ml_kem_512_ref_keypair_derand(&params, public_key, secret_key, seed);
}

int ml_kem_512_ipd_keypair(uint8_t *public_key /* OUT */,
                           uint8_t *secret_key /* OUT */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);
  return ml_kem_512_ref_keypair(&params, public_key, secret_key);
}

int ml_kem_512_ipd_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed       /* IN */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);
  return ml_kem_512_ref_enc_derand(&params, ciphertext, shared_secret, public_key, seed);
}

int ml_kem_512_ipd_encapsulate(uint8_t *ciphertext       /* OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               const uint8_t *public_key /* IN  */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);
  return ml_kem_512_ref_enc(&params, ciphertext, shared_secret, public_key);
}

int ml_kem_512_ipd_decapsulate(uint8_t *shared_secret    /* OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);
  return ml_kem_512_ref_dec(&params, shared_secret, ciphertext, secret_key);
}

int ml_kem_768_ipd_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                         uint8_t *secret_key  /* OUT */,
                                         const uint8_t *seed  /* IN */) {
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  return ml_kem_768_ref_keypair_derand(&params, public_key, secret_key, seed);
}

int ml_kem_768_ipd_keypair(uint8_t *public_key /* OUT */,
                           uint8_t *secret_key /* OUT */) {
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  return ml_kem_768_ref_keypair(&params, public_key, secret_key);
}

int ml_kem_768_ipd_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed       /* IN */) {
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  return ml_kem_768_ref_enc_derand(&params, ciphertext, shared_secret, public_key, seed);
}

int ml_kem_768_ipd_encapsulate(uint8_t *ciphertext       /* OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               const uint8_t *public_key /* IN  */) {
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  return ml_kem_768_ref_enc(&params, ciphertext, shared_secret, public_key);
}

int ml_kem_768_ipd_decapsulate(uint8_t *shared_secret    /* OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */) {
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  return ml_kem_768_ref_dec(&params, shared_secret, ciphertext, secret_key);
}

int ml_kem_1024_ipd_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                          uint8_t *secret_key  /* OUT */,
                                          const uint8_t *seed  /* IN */) {
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  return ml_kem_1024_ref_keypair_derand(&params, public_key, secret_key, seed);
}

int ml_kem_1024_ipd_keypair(uint8_t *public_key /* OUT */,
                            uint8_t *secret_key /* OUT */) {
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  return ml_kem_1024_ref_keypair(&params, public_key, secret_key);
}

int ml_kem_1024_ipd_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                              uint8_t *shared_secret    /* OUT */,
                                              const uint8_t *public_key /* IN  */,
                                              const uint8_t *seed       /* IN */) {
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  return ml_kem_1024_ref_enc_derand(&params, ciphertext, shared_secret, public_key, seed);
}

int ml_kem_1024_ipd_encapsulate(uint8_t *ciphertext       /* OUT */,
                                uint8_t *shared_secret    /* OUT */,
                                const uint8_t *public_key /* IN  */) {
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  return ml_kem_1024_ref_enc(&params, ciphertext, shared_secret, public_key);
}

int ml_kem_1024_ipd_decapsulate(uint8_t *shared_secret    /* OUT */,
                                const uint8_t *ciphertext /* IN  */,
                                const uint8_t *secret_key /* IN  */) {
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  return ml_kem_1024_ref_dec(&params, shared_secret, ciphertext, secret_key);
}
