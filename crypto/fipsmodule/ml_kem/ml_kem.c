// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// mlkem-native source code

// Include level-independent code
#define MLK_CONFIG_FILE "../mlkem_native_config.h"
#define MLK_CONFIG_FIPS202_CUSTOM_HEADER "../fips202_glue.h"
#define MLK_CONFIG_FIPS202X4_CUSTOM_HEADER "../fips202x4_glue.h"
#define MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS

// MLKEM-512
#define MLK_CONFIG_PARAMETER_SET 512
#define MLK_CONFIG_MULTILEVEL_WITH_SHARED // Include level-independent code
#include "mlkem/mlkem_native_bcm.c"
// MLKEM-768
#undef MLK_CONFIG_PARAMETER_SET
#define MLK_CONFIG_PARAMETER_SET 768
#define MLK_CONFIG_MULTILEVEL_NO_SHARED // Exclude level-inpendent code
#include "mlkem/mlkem_native_bcm.c"
// MLKEM-1024
#undef MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#undef MLK_CONFIG_PARAMETER_SET
#define MLK_CONFIG_PARAMETER_SET 1024
#include "mlkem/mlkem_native_bcm.c"

// End of mlkem-native source code

#include "./ml_kem.h"

// Ensure buffer is long enough and zero any extra memory
int check_buffer(const uint8_t *buffer, const size_t len, const size_t expeted_len);

// EVP layer assumes the length parameter passed in will be set to the number of bytes written if call is successful
void set_written_len_on_success(const int result, size_t *length, const size_t written_len);

int ml_kem_common_keypair(int (*keypair)(uint8_t * public_key, uint8_t *secret_key),
                          uint8_t *public_key,
                          size_t *public_len,
                          const size_t expected_public_len,
                          uint8_t *secret_key,
                          size_t *secret_len,
                          const size_t expected_secret_len);

int ml_kem_common_encapsulate_deterministic(int (*encapsulate)(uint8_t *ciphertext, uint8_t *shared_secret, const uint8_t *public_key, const uint8_t *seed),
                                            uint8_t *ciphertext,
                                            size_t *ciphertext_len,
                                            const size_t expected_ciphertext_len,
                                            uint8_t *shared_secret,
                                            size_t *shared_secret_len,
                                            const size_t expected_shared_secret_len,
                                            const uint8_t *public_key,
                                            const uint8_t *seed);

int ml_kem_common_encapsulate(int (*encapsulate)(uint8_t *ciphertext, uint8_t *shared_secret, const uint8_t *public_key),
                              uint8_t *ciphertext,
                              size_t *ciphertext_len,
                              const size_t expected_ciphertext_len,
                              uint8_t *shared_secret,
                              size_t *shared_secret_len,
                              const size_t expected_shared_secret_len,
                              const uint8_t *public_key);

int ml_kem_common_decapsulate(int (*decapsulate)(uint8_t *shared_secret, const uint8_t *ciphertext, const uint8_t *secret_key),
                              uint8_t *shared_secret,
                              size_t *shared_secret_len,
                              const size_t expected_shared_secret_len,
                              const uint8_t *ciphertext,
                              const uint8_t *secret_key);

// Note: These methods currently default to using the reference code for ML_KEM.
// In a future where AWS-LC has optimized options available, those can be
// conditionally (or based on compile-time flags) called here, depending on
// platform support.

int ml_kem_512_keypair_deterministic(uint8_t *public_key /* OUT */,
                                     size_t *public_len  /* IN_OUT */,
                                     uint8_t *secret_key /* OUT */,
                                     size_t *secret_len  /* IN_OUT */,
                                     const uint8_t *seed /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_512_keypair_deterministic_no_self_test(public_key, public_len, secret_key, secret_len, seed);
}

int ml_kem_512_keypair_deterministic_no_self_test(uint8_t *public_key  /* OUT */,
                                                  size_t *public_len  /* IN_OUT */,
                                                  uint8_t *secret_key  /* OUT */,
                                                  size_t *secret_len  /* IN_OUT */,
                                                  const uint8_t *seed  /* IN */) {
  if (!check_buffer(public_key, *public_len, MLKEM512_PUBLIC_KEY_BYTES) ||
      !check_buffer(secret_key, *secret_len, MLKEM512_SECRET_KEY_BYTES)) {
    return 1;
  }
  const int res = mlkem512_keypair_derand(public_key, secret_key, seed);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
    AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  set_written_len_on_success(res, public_len, MLKEM512_PUBLIC_KEY_BYTES);
  set_written_len_on_success(res, secret_len, MLKEM512_SECRET_KEY_BYTES);
  return res;
}

int ml_kem_512_keypair(uint8_t *public_key /* OUT */,
                       size_t *public_len  /* IN_OUT */,
                       uint8_t *secret_key /* OUT */,
                       size_t *secret_len  /* IN_OUT */) {
  return ml_kem_common_keypair(mlkem512_keypair,
                               public_key, public_len, MLKEM512_PUBLIC_KEY_BYTES,
                               secret_key, secret_len, MLKEM512_SECRET_KEY_BYTES);
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
                                                      const uint8_t *public_key /* IN */,
                                                      const uint8_t *seed       /* IN */) {
  return ml_kem_common_encapsulate_deterministic(mlkem512_enc_derand, ciphertext, ciphertext_len, MLKEM512_CIPHERTEXT_BYTES, shared_secret, shared_secret_len, MLKEM512_SHARED_SECRET_LEN, public_key, seed);
}

int ml_kem_512_encapsulate(uint8_t *ciphertext       /* OUT */,
                           size_t *ciphertext_len    /* IN_OUT */,
                           uint8_t *shared_secret    /* OUT */,
                           size_t *shared_secret_len /* IN_OUT */,
                           const uint8_t *public_key /* IN */) {
  return ml_kem_common_encapsulate(mlkem512_enc, ciphertext, ciphertext_len, MLKEM512_CIPHERTEXT_BYTES, shared_secret, shared_secret_len, MLKEM512_SHARED_SECRET_LEN, public_key);
}

int ml_kem_512_decapsulate(uint8_t *shared_secret    /* OUT */,
                           size_t *shared_secret_len /* IN_OUT */,
                           const uint8_t *ciphertext /* IN */,
                           const uint8_t *secret_key /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_512_decapsulate_no_self_test(shared_secret, shared_secret_len, ciphertext, secret_key);
}

int ml_kem_512_decapsulate_no_self_test(uint8_t *shared_secret    /* OUT */,
                                        size_t *shared_secret_len /* IN_OUT */,
                                        const uint8_t *ciphertext /* IN  */,
                                        const uint8_t *secret_key /* IN  */) {
  return ml_kem_common_decapsulate(mlkem512_dec, shared_secret, shared_secret_len, MLKEM512_SHARED_SECRET_LEN, ciphertext, secret_key);
}


int ml_kem_768_keypair_deterministic(uint8_t *public_key /* OUT */,
                                     size_t *public_len  /* IN_OUT */,
                                     uint8_t *secret_key /* OUT */,
                                     size_t *secret_len  /* IN_OUT */,
                                     const uint8_t *seed /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_768_keypair_deterministic_no_self_test(public_key, public_len, secret_key, secret_len, seed);
}


int ml_kem_768_keypair_deterministic_no_self_test(uint8_t *public_key /* OUT */,
                                                  size_t *public_len  /* IN_OUT */,
                                                  uint8_t *secret_key /* OUT */,
                                                  size_t *secret_len  /* IN_OUT */,
                                                  const uint8_t *seed /* IN */) {
  if (!check_buffer(public_key, *public_len, MLKEM768_PUBLIC_KEY_BYTES) ||
      !check_buffer(secret_key, *secret_len, MLKEM768_SECRET_KEY_BYTES)) {
    return 1;
  }
  const int res = mlkem768_keypair_derand(public_key, secret_key, seed);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
    AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  set_written_len_on_success(res, public_len, MLKEM768_PUBLIC_KEY_BYTES);
  set_written_len_on_success(res, secret_len, MLKEM768_SECRET_KEY_BYTES);
  return res;
}

int ml_kem_768_keypair(uint8_t *public_key /* OUT */,
                       size_t *public_len  /* IN_OUT */,
                       uint8_t *secret_key /* OUT */,
                       size_t *secret_len  /* IN_OUT */) {
  return ml_kem_common_keypair(mlkem768_keypair,
                               public_key, public_len, MLKEM768_PUBLIC_KEY_BYTES,
                               secret_key, secret_len, MLKEM768_SECRET_KEY_BYTES);
}

int ml_kem_768_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                         size_t *ciphertext_len    /* IN_OUT */,
                                         uint8_t *shared_secret    /* OUT */,
                                         size_t *shared_secret_len /* IN_OUT */,
                                         const uint8_t *public_key /* IN */,
                                         const uint8_t *seed       /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_768_encapsulate_deterministic_no_self_test(ciphertext, ciphertext_len, shared_secret, shared_secret_len, public_key, seed);
}

int ml_kem_768_encapsulate_deterministic_no_self_test(uint8_t *ciphertext       /* OUT */,
                                                      size_t *ciphertext_len    /* IN_OUT */,
                                                      uint8_t *shared_secret    /* OUT */,
                                                      size_t *shared_secret_len /* IN_OUT */,
                                                      const uint8_t *public_key /* IN */,
                                                      const uint8_t *seed       /* IN */) {
  return ml_kem_common_encapsulate_deterministic(mlkem768_enc_derand, ciphertext, ciphertext_len, MLKEM768_CIPHERTEXT_BYTES, shared_secret, shared_secret_len, MLKEM768_SHARED_SECRET_LEN, public_key, seed);
}

int ml_kem_768_encapsulate(uint8_t *ciphertext       /* OUT */,
                           size_t *ciphertext_len    /* IN_OUT */,
                           uint8_t *shared_secret    /* OUT */,
                           size_t *shared_secret_len /* IN_OUT */,
                           const uint8_t *public_key /* IN */) {
  return ml_kem_common_encapsulate(mlkem768_enc, ciphertext, ciphertext_len, MLKEM768_CIPHERTEXT_BYTES, shared_secret, shared_secret_len, MLKEM768_SHARED_SECRET_LEN, public_key);
}

int ml_kem_768_decapsulate(uint8_t *shared_secret    /* OUT */,
                           size_t *shared_secret_len /* IN_OUT */,
                           const uint8_t *ciphertext /* IN */,
                           const uint8_t *secret_key /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_768_decapsulate_no_self_test(shared_secret, shared_secret_len, ciphertext, secret_key);
}

int ml_kem_768_decapsulate_no_self_test(uint8_t *shared_secret    /* OUT */,
                           size_t *shared_secret_len /* IN_OUT */,
                           const uint8_t *ciphertext /* IN */,
                           const uint8_t *secret_key /* IN */) {
  return ml_kem_common_decapsulate(mlkem768_dec, shared_secret, shared_secret_len, MLKEM768_SHARED_SECRET_LEN, ciphertext, secret_key);
}

int ml_kem_1024_keypair_deterministic(uint8_t *public_key /* OUT */,
                                      size_t *public_len  /* IN_OUT */,
                                      uint8_t *secret_key /* OUT */,
                                      size_t *secret_len  /* IN_OUT */,
                                      const uint8_t *seed /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_1024_keypair_deterministic_no_self_test(public_key, public_len, secret_key, secret_len, seed);
}

int ml_kem_1024_keypair_deterministic_no_self_test(uint8_t *public_key /* OUT */,
                                      size_t *public_len  /* IN_OUT */,
                                      uint8_t *secret_key /* OUT */,
                                      size_t *secret_len  /* IN_OUT */,
                                      const uint8_t *seed /* IN */) {
  if (!check_buffer(public_key, *public_len, MLKEM1024_PUBLIC_KEY_BYTES) ||
      !check_buffer(secret_key, *secret_len, MLKEM1024_SECRET_KEY_BYTES)) {
    return 1;
      }
  const int res = mlkem1024_keypair_derand(public_key, secret_key, seed);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
    AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  set_written_len_on_success(res, public_len, MLKEM1024_PUBLIC_KEY_BYTES);
  set_written_len_on_success(res, secret_len, MLKEM1024_SECRET_KEY_BYTES);
  return res;
}

int ml_kem_1024_keypair(uint8_t *public_key /* OUT */,
                        size_t *public_len  /* IN_OUT */,
                        uint8_t *secret_key /* OUT */,
                        size_t *secret_len  /* IN_OUT */) {
  return ml_kem_common_keypair(mlkem1024_keypair,
                               public_key, public_len, MLKEM1024_PUBLIC_KEY_BYTES,
                               secret_key, secret_len, MLKEM1024_SECRET_KEY_BYTES);
}

int ml_kem_1024_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                          size_t *ciphertext_len    /* IN_OUT */,
                                          uint8_t *shared_secret    /* OUT */,
                                          size_t *shared_secret_len /* IN_OUT */,
                                          const uint8_t *public_key /* IN */,
                                          const uint8_t *seed       /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_1024_encapsulate_deterministic_no_self_test(ciphertext, ciphertext_len, shared_secret, shared_secret_len, public_key, seed);
}

int ml_kem_1024_encapsulate_deterministic_no_self_test(uint8_t *ciphertext       /* OUT */,
                                                       size_t *ciphertext_len    /* IN_OUT */,
                                                       uint8_t *shared_secret    /* OUT */,
                                                       size_t *shared_secret_len /* IN_OUT */,
                                                       const uint8_t *public_key /* IN */,
                                                       const uint8_t *seed       /* IN */) {
  return ml_kem_common_encapsulate_deterministic(mlkem1024_enc_derand, ciphertext, ciphertext_len, MLKEM1024_CIPHERTEXT_BYTES, shared_secret, shared_secret_len, MLKEM1024_SHARED_SECRET_LEN, public_key, seed);
}

int ml_kem_1024_encapsulate(uint8_t *ciphertext       /* OUT */,
                            size_t *ciphertext_len    /* IN_OUT */,
                            uint8_t *shared_secret    /* OUT */,
                            size_t *shared_secret_len /* IN_OUT */,
                            const uint8_t *public_key /* IN */) {
  return ml_kem_common_encapsulate(mlkem1024_enc, ciphertext, ciphertext_len, MLKEM1024_CIPHERTEXT_BYTES, shared_secret, shared_secret_len, MLKEM1024_SHARED_SECRET_LEN, public_key);
}

int ml_kem_1024_decapsulate(uint8_t *shared_secret    /* OUT */,
                            size_t *shared_secret_len /* IN_OUT */,
                            const uint8_t *ciphertext /* IN */,
                            const uint8_t *secret_key /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_1024_decapsulate_no_self_test(shared_secret, shared_secret_len, ciphertext, secret_key);
}

int ml_kem_1024_decapsulate_no_self_test(uint8_t *shared_secret    /* OUT */,
                            size_t *shared_secret_len /* IN_OUT */,
                            const uint8_t *ciphertext /* IN */,
                            const uint8_t *secret_key /* IN */) {
  return ml_kem_common_decapsulate(mlkem1024_dec, shared_secret, shared_secret_len, MLKEM1024_SHARED_SECRET_LEN, ciphertext, secret_key);
}


int check_buffer(const uint8_t *buffer, const size_t len, const size_t expected_len) {
  if (buffer == NULL || len < expected_len) {
    return 0;
  }
  return 1;
}

void set_written_len_on_success(const int result, size_t *length, const size_t written_len) {
  if (result == 0) {
    *length = written_len;
  }
}

int ml_kem_common_keypair(int (*keypair)(uint8_t * public_key, uint8_t *secret_key),
                          uint8_t *public_key,
                          size_t *public_len,
                          const size_t expected_public_len,
                          uint8_t *secret_key,
                          size_t *secret_len,
                          const size_t expected_secret_len) {
  boringssl_ensure_ml_kem_self_test();
  if (!check_buffer(public_key, *public_len, expected_public_len) ||
      !check_buffer(secret_key, *secret_len, expected_secret_len)) {
    return 1;
  }
  const int res = keypair(public_key, secret_key);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
    AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  set_written_len_on_success(res, public_len, expected_public_len);
  set_written_len_on_success(res, secret_len, expected_secret_len);
  return res;
}

int ml_kem_common_encapsulate_deterministic(int (*encapsulate)(uint8_t *ciphertext, uint8_t *shared_secret, const uint8_t *public_key, const uint8_t *seed),
                                            uint8_t *ciphertext, size_t *ciphertext_len, const size_t expected_ciphertext_len,
                                            uint8_t *shared_secret, size_t *shared_secret_len, const size_t expected_shared_secret_len,
                                            const uint8_t *public_key, const uint8_t *seed) {
  if (!check_buffer(ciphertext, *ciphertext_len, expected_ciphertext_len) ||
      !check_buffer(shared_secret, *shared_secret_len, expected_shared_secret_len)) {
    return 1;
  }
  const int res = encapsulate(ciphertext, shared_secret, public_key, seed);
  set_written_len_on_success(res, ciphertext_len, expected_ciphertext_len);
  set_written_len_on_success(res, shared_secret_len, expected_shared_secret_len);
  return res;
}

int ml_kem_common_encapsulate(int (*encapsulate)(uint8_t *ciphertext, uint8_t *shared_secret, const uint8_t *public_key),
                              uint8_t *ciphertext, size_t *ciphertext_len, const size_t expected_ciphertext_len,
                              uint8_t *shared_secret, size_t *shared_secret_len, const size_t expected_shared_secret_len,
                              const uint8_t *public_key) {
  boringssl_ensure_ml_kem_self_test();
  if (!check_buffer(ciphertext, *ciphertext_len, expected_ciphertext_len) ||
      !check_buffer(shared_secret, *shared_secret_len, expected_shared_secret_len)) {
    return 1;
  }
  const int res = encapsulate(ciphertext, shared_secret, public_key);
  set_written_len_on_success(res, ciphertext_len, expected_ciphertext_len);
  set_written_len_on_success(res, shared_secret_len, expected_shared_secret_len);
  return res;
}

int ml_kem_common_decapsulate(int (*decapsulate)(uint8_t *shared_secret, const uint8_t *ciphertext, const uint8_t *secret_key), uint8_t *shared_secret, size_t *shared_secret_len, const size_t expected_shared_secret_len, const uint8_t *ciphertext, const uint8_t *secret_key) {
  if (!check_buffer(shared_secret, *shared_secret_len, expected_shared_secret_len)) {
    return 1;
  }
  const int res = decapsulate(shared_secret, ciphertext, secret_key);
  set_written_len_on_success(res, shared_secret_len, expected_shared_secret_len);
  return res;
}
