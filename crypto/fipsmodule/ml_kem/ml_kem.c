// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "./ml_kem.h"

#include "./ml_kem_ref/kem.h"
#include "./ml_kem_ref/params.h"

#include "./ml_kem_ref/cbd.c"
#include "./ml_kem_ref/indcpa.c"
#include "./ml_kem_ref/kem.c"
#include "./ml_kem_ref/ntt.c"
#include "./ml_kem_ref/params.c"
#include "./ml_kem_ref/poly.c"
#include "./ml_kem_ref/polyvec.c"
#include "./ml_kem_ref/reduce.c"
#include "./ml_kem_ref/symmetric-shake.c"
#include "./ml_kem_ref/verify.c"

// Note: These methods currently default to using the reference code for ML_KEM.
// In a future where AWS-LC has optimized options available, those can be
// conditionally (or based on compile-time flags) called here, depending on
// platform support.

int ml_kem_512_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                         size_t *public_len /* IN_OUT */,
                                         uint8_t *secret_key  /* OUT */,
                                         size_t *secret_len /* IN_OUT */,
                                         const uint8_t *seed  /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_512_keypair_deterministic_no_self_test(public_key, public_len, secret_key, secret_len, seed);
}

int ml_kem_512_keypair_deterministic_no_self_test(uint8_t *public_key  /* OUT */,
                                                  size_t *public_len /* IN_OUT */,
                                                  uint8_t *secret_key  /* OUT */,
                                                  size_t *secret_len /* IN_OUT */,
                                                  const uint8_t *seed  /* IN */) {
  ml_kem_params params;
  int res;
  ml_kem_512_params_init(&params);
  if (*public_len < params.public_key_bytes || *secret_len < params.secret_key_bytes) {
    return 0;
  }
  res = ml_kem_keypair_derand_ref(&params, public_key, secret_key, seed);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  if (res == 0) {
    *public_len = params.public_key_bytes;
    *secret_len = params.secret_key_bytes;
  }
  return res;
}

int ml_kem_512_keypair(uint8_t *public_key /* OUT */,
                           size_t *public_len /* IN_OUT */,
                           uint8_t *secret_key /* OUT */,
                           size_t *secret_len /* IN_OUT */) {
  boringssl_ensure_ml_kem_self_test();
  int res;
  ml_kem_params params;
  ml_kem_512_params_init(&params);
  if (*public_len < params.public_key_bytes || *secret_len < params.secret_key_bytes) {
    return 0;
  }
  res = ml_kem_keypair_ref(&params, public_key, secret_key);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  if (res == 0) {
    *public_len = params.public_key_bytes;
    *secret_len = params.secret_key_bytes;
  }
  return res;
}

int ml_kem_512_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             size_t *ciphertext_len    /* IN_OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             size_t *shared_secret_len /* IN_OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed       /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_512_encapsulate_deterministic_no_self_test(ciphertext, ciphertext_len, shared_secret, shared_secret_len, public_key, seed);
}

int ml_kem_512_encapsulate_deterministic_no_self_test(uint8_t *ciphertext       /* OUT */,
                                                      size_t *ciphertext_len    /* IN_OUT */,
                                                      uint8_t *shared_secret    /* OUT */,
                                                      size_t *shared_secret_len /* IN_OUT */,
                                                      const uint8_t *public_key /* IN  */,
                                                      const uint8_t *seed       /* IN */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);

  if (*ciphertext_len < params.ciphertext_bytes ||
      *shared_secret_len < params.shared_secret_bytes) {
    return 0;
  }

  const int res = ml_kem_enc_derand_ref(&params, ciphertext, shared_secret, public_key,
                               seed);

  if (res != 0) {
    *ciphertext_len = params.ciphertext_bytes;
    *shared_secret_len = params.shared_secret_bytes;
  }

  return res;
}

int ml_kem_512_encapsulate(uint8_t *ciphertext       /* OUT */,
                               size_t *ciphertext_len    /* IN_OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               size_t *shared_secret_len /* IN_OUT */,
                               const uint8_t *public_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  ml_kem_params params;
  ml_kem_512_params_init(&params);

  if (*ciphertext_len < params.ciphertext_bytes ||
      *shared_secret_len < params.shared_secret_bytes) {
    return 0;
  }

  const int res = ml_kem_enc_ref(&params, ciphertext, shared_secret, public_key);

  if (res != 0) {
    *ciphertext_len = params.ciphertext_bytes;
    *shared_secret_len = params.shared_secret_bytes;
  }

  return res;
}

int ml_kem_512_decapsulate(uint8_t *shared_secret    /* OUT */,
                               size_t *shared_secret_len /* IN_OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_512_decapsulate_no_self_test(shared_secret, shared_secret_len, ciphertext, secret_key);
}

int ml_kem_512_decapsulate_no_self_test(uint8_t *shared_secret    /* OUT */,
                                        size_t *shared_secret_len /* IN_OUT */,
                                        const uint8_t *ciphertext /* IN  */,
                                        const uint8_t *secret_key /* IN  */) {
  ml_kem_params params;
  ml_kem_512_params_init(&params);

  if (*shared_secret_len < params.shared_secret_bytes) {
    return 0;
  }

  const int res = ml_kem_dec_ref(&params, shared_secret, ciphertext, secret_key);

  if (res != 0) {
    *shared_secret_len = params.shared_secret_bytes;
  }

  return res;
}


int ml_kem_768_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                         size_t *public_len /* IN_OUT */,
                                         uint8_t *secret_key  /* OUT */,
                                         size_t *secret_len /* IN_OUT */,
                                         const uint8_t *seed  /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  ml_kem_params params;
  int res;
  ml_kem_768_params_init(&params);
  if (*public_len < params.public_key_bytes || *secret_len < params.secret_key_bytes) {
    return 0;
  }
  res = ml_kem_keypair_derand_ref(&params, public_key, secret_key, seed);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  if (res == 0) {
    *public_len = params.public_key_bytes;
    *secret_len = params.secret_key_bytes;
  }
  return res;
}

int ml_kem_768_keypair(uint8_t *public_key /* OUT */,
                           size_t *public_len /* IN_OUT */,
                           uint8_t *secret_key /* OUT */,
                           size_t *secret_len /* IN_OUT */) {
  boringssl_ensure_ml_kem_self_test();
  ml_kem_params params;
  int res;
  ml_kem_768_params_init(&params);
  if (*public_len < params.public_key_bytes || *secret_len < params.secret_key_bytes) {
    return 0;
  }
  res = ml_kem_keypair_ref(&params, public_key, secret_key);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  if (res == 0) {
    *public_len = params.public_key_bytes;
    *secret_len = params.secret_key_bytes;
  }
  return res;
}

int ml_kem_768_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             size_t *ciphertext_len /* IN_OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             size_t *shared_secret_len /* IN_OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed       /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  if (*ciphertext_len < params.ciphertext_bytes || *shared_secret_len < params.shared_secret_bytes) {
    return 0;
  }
  const int res = ml_kem_enc_derand_ref(&params, ciphertext, shared_secret, public_key, seed);
  if (res != 0) {
    *ciphertext_len = params.ciphertext_bytes;
    *shared_secret_len = params.shared_secret_bytes;
  }
  return res;
}

int ml_kem_768_encapsulate(uint8_t *ciphertext       /* OUT */,
                               size_t *ciphertext_len /* IN_OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               size_t *shared_secret_len /* IN_OUT */,
                               const uint8_t *public_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  if (*ciphertext_len < params.ciphertext_bytes || *shared_secret_len < params.shared_secret_bytes) {
    return 0;
  }
  const int res = ml_kem_enc_ref(&params, ciphertext, shared_secret, public_key);
  if (res != 0) {
    *ciphertext_len = params.ciphertext_bytes;
    *shared_secret_len = params.shared_secret_bytes;
  }
  return res;
}

int ml_kem_768_decapsulate(uint8_t *shared_secret    /* OUT */,
                               size_t *shared_secret_len /* IN_OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  ml_kem_params params;
  ml_kem_768_params_init(&params);
  if (*shared_secret_len < params.shared_secret_bytes) {
    return 0;
  }
  const int res = ml_kem_dec_ref(&params, shared_secret, ciphertext, secret_key);
  if (res != 0) {
    *shared_secret_len = params.shared_secret_bytes;
  }
  return res;
}

int ml_kem_1024_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                          size_t *public_len /* IN_OUT */,
                                          uint8_t *secret_key  /* OUT */,
                                          size_t *secret_len /* IN_OUT */,
                                          const uint8_t *seed  /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  ml_kem_params params;
  int res;
  ml_kem_1024_params_init(&params);
  if (*public_len < params.public_key_bytes || *secret_len < params.secret_key_bytes) {
    return 0;
  }
  res = ml_kem_keypair_derand_ref(&params, public_key, secret_key, seed);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  if (res == 0) {
    *public_len = params.public_key_bytes;
    *secret_len = params.secret_key_bytes;
  }
  return res;
}

int ml_kem_1024_keypair(uint8_t *public_key /* OUT */,
                            size_t *public_len /* IN_OUT */,
                            uint8_t *secret_key /* OUT */,
                            size_t *secret_len /* IN_OUT */) {
  boringssl_ensure_ml_kem_self_test();
  ml_kem_params params;
  int res;
  ml_kem_1024_params_init(&params);
  if (*public_len < params.public_key_bytes || *secret_len < params.secret_key_bytes) {
    return 0;
  }
  res = ml_kem_keypair_ref(&params, public_key, secret_key);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  if (res == 0) {
    *public_len = params.public_key_bytes;
    *secret_len = params.secret_key_bytes;
  }
  return res;
}

int ml_kem_1024_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                              size_t *ciphertext_len /* IN_OUT */,
                                              uint8_t *shared_secret    /* OUT */,
                                              size_t *shared_secret_len /* IN_OUT */,
                                              const uint8_t *public_key /* IN  */,
                                              const uint8_t *seed       /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  if (*ciphertext_len < params.ciphertext_bytes || *shared_secret_len < params.shared_secret_bytes) {
    return 0;
  }
  const int res = ml_kem_enc_derand_ref(&params, ciphertext, shared_secret, public_key, seed);
  if (res != 0) {
    *ciphertext_len = params.ciphertext_bytes;
    *shared_secret_len = params.shared_secret_bytes;
  }
  return res;
}

int ml_kem_1024_encapsulate(uint8_t *ciphertext       /* OUT */,
                                size_t *ciphertext_len /* IN_OUT */,
                                uint8_t *shared_secret    /* OUT */,
                                size_t *shared_secret_len /* IN_OUT */,
                                const uint8_t *public_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  if (*ciphertext_len < params.ciphertext_bytes || *shared_secret_len < params.shared_secret_bytes) {
    return 0;
  }
  const int res = ml_kem_enc_ref(&params, ciphertext, shared_secret, public_key);
  if (res != 0) {
    *ciphertext_len = params.ciphertext_bytes;
    *shared_secret_len = params.shared_secret_bytes;
  }
  return res;
}

int ml_kem_1024_decapsulate(uint8_t *shared_secret    /* OUT */,
                                size_t *shared_secret_len /* IN_OUT */,
                                const uint8_t *ciphertext /* IN  */,
                                const uint8_t *secret_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  ml_kem_params params;
  ml_kem_1024_params_init(&params);
  if (*shared_secret_len < params.shared_secret_bytes) {
    return 0;
  }
  const int res = ml_kem_dec_ref(&params, shared_secret, ciphertext, secret_key);
  if (res != 0) {
    *shared_secret_len = params.shared_secret_bytes;
  }
  return res;
}
