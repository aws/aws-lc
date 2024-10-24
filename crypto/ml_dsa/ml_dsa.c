// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
#include "../evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "ml_dsa.h"
#include "ml_dsa_ref/sign.h"
#include "ml_dsa_ref/params.h"
#include "../nistdsa/internal.h"

// These includes are required to compile ML-DSA. These can be moved to bcm.c
// when ML-DSA is added to the fipsmodule directory.
#include "./ml_dsa_ref/fips202.c"
#include "./ml_dsa_ref/ntt.c"
#include "./ml_dsa_ref/packing.c"
#include "./ml_dsa_ref/params.c"
#include "./ml_dsa_ref/poly.c"
#include "./ml_dsa_ref/polyvec.c"
#include "./ml_dsa_ref/reduce.c"
#include "./ml_dsa_ref/rounding.c"
#include "./ml_dsa_ref/sign.c"
#include "./ml_dsa_ref/symmetric-shake.c"

// Note: These methods currently default to using the reference code for
// ML-DSA. In a future where AWS-LC has optimized options available,
// those can be conditionally (or based on compile-time flags) called here,
// depending on platform support.

int ml_dsa_44_keypair(uint8_t *public_key,
                      uint8_t *secret_key) {
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return (crypto_sign_keypair(&params, public_key, secret_key) == 0);
}

int ml_dsa_44_sign(uint8_t *sig, size_t *sig_len,
                   const uint8_t *message,
                   size_t message_len,
                   const uint8_t *ctx,
                   size_t ctx_len,
                   const uint8_t *secret_key) {
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return crypto_sign_signature(&params, sig, sig_len, message, message_len,
                                             ctx, ctx_len, secret_key);
}

int ml_dsa_44_verify(const uint8_t *message,
                     size_t message_len,
                     const uint8_t *sig,
                     size_t sig_len,
                     const uint8_t *ctx,
                     size_t ctx_len,
                     const uint8_t *public_key) {
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return crypto_sign_verify(&params, sig, sig_len, message, message_len,
                                        ctx, ctx_len, public_key);
}

int ml_dsa_65_keypair(uint8_t *public_key  /* OUT */,
                       uint8_t *secret_key /* OUT */) {
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return (crypto_sign_keypair(&params, public_key, secret_key) == 0);
}

int ml_dsa_65_sign(uint8_t *sig                /* OUT */,
                    size_t *sig_len            /* OUT */,
                    const uint8_t *message     /* IN */,
                    size_t message_len         /* IN */,
                    const uint8_t *ctx         /* IN */,
                    size_t ctx_len             /* IN */,
                    const uint8_t *secret_key  /* IN */) {
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return crypto_sign_signature(&params, sig, sig_len, message, message_len,
                                             ctx, ctx_len, secret_key);
}

int ml_dsa_65_verify(const uint8_t *message     /* IN */,
                      size_t message_len        /* IN */,
                      const uint8_t *sig        /* IN */,
                      size_t sig_len            /* IN */,
                      const uint8_t *ctx        /* IN */,
                      size_t ctx_len            /* IN */,
                      const uint8_t *public_key /* IN */) {
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return crypto_sign_verify(&params, sig, sig_len, message, message_len,
                                          ctx, ctx_len, public_key);
}

int ml_dsa_87_keypair(uint8_t *public_key,
                      uint8_t *secret_key) {
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return (crypto_sign_keypair(&params, public_key, secret_key) == 0);
}

int ml_dsa_87_sign(uint8_t *sig, size_t *sig_len,
                   const uint8_t *message,
                   size_t message_len,
                   const uint8_t *ctx,
                   size_t ctx_len,
                   const uint8_t *secret_key) {
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return crypto_sign_signature(&params, sig, sig_len, message, message_len,
                                             ctx, ctx_len, secret_key);
}

int ml_dsa_87_verify(const uint8_t *message,
                     size_t message_len,
                     const uint8_t *sig,
                     size_t sig_len,
                     const uint8_t *ctx,
                     size_t ctx_len,
                     const uint8_t *public_key) {
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return crypto_sign_verify(&params, sig, sig_len, message, message_len,
                                        ctx, ctx_len, public_key);
}
