// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

/* mlkem-native source code */

/* Include level-independent code */
#define MLK_CONFIG_FILE "../mlkem_native_config.h"
#define MLK_FIPS202_CUSTOM_HEADER "../fips202_glue.h"
#define MLK_FIPS202X4_CUSTOM_HEADER "../fips202x4_glue.h"

/* MLKEM-512 */
#define MLKEM_K 2
#define MLK_MULTILEVEL_BUILD_WITH_SHARED /* Include level-independent code */
#define MLK_MONOBUILD_KEEP_SHARED_HEADERS
#include "mlkem/mlkem_native_bcm.c"
/* MLKEM-768 */
#define MLKEM_K 3
#define MLK_MULTILEVEL_BUILD_NO_SHARED /* Exclude levelinpendent code */
#define MLK_MONOBUILD_KEEP_SHARED_HEADERS
#include "mlkem/mlkem_native_bcm.c"
/* MLKEM-1024 */
#define MLKEM_K 4
#undef MLK_MONOBUILD_KEEP_SHARED_HEADERS
#include "mlkem/mlkem_native_bcm.c"

/* End of mlkem-native source code */

#include "./ml_kem.h"
#include "openssl/rand.h"

void randombytes(uint8_t *out, size_t outlen)
{
    RAND_bytes(out, outlen);
}

int ml_kem_512_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                         uint8_t *secret_key  /* OUT */,
                                         const uint8_t *seed  /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_512_keypair_deterministic_no_self_test(public_key, secret_key, seed);
}

int ml_kem_512_keypair_deterministic_no_self_test(uint8_t *public_key  /* OUT */,
                                                  uint8_t *secret_key  /* OUT */,
                                                  const uint8_t *seed  /* IN */) {
  int res = mlkem512_keypair_derand(public_key, secret_key, seed);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  return res;
}

int ml_kem_512_keypair(uint8_t *public_key /* OUT */,
                           uint8_t *secret_key /* OUT */) {
  boringssl_ensure_ml_kem_self_test();
  int res = mlkem512_keypair(public_key, secret_key);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  return res;
}

int ml_kem_512_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed       /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_512_encapsulate_deterministic_no_self_test(ciphertext, shared_secret, public_key, seed);
}

int ml_kem_512_encapsulate_deterministic_no_self_test(uint8_t *ciphertext       /* OUT */,
                                                      uint8_t *shared_secret    /* OUT */,
                                                      const uint8_t *public_key /* IN  */,
                                                      const uint8_t *seed       /* IN */) {
  return mlkem512_enc_derand(ciphertext, shared_secret, public_key, seed);
}

int ml_kem_512_encapsulate(uint8_t *ciphertext       /* OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               const uint8_t *public_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  return mlkem512_enc(ciphertext, shared_secret, public_key);
}

int ml_kem_512_decapsulate(uint8_t *shared_secret    /* OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  return ml_kem_512_decapsulate_no_self_test(shared_secret, ciphertext, secret_key);
}

int ml_kem_512_decapsulate_no_self_test(uint8_t *shared_secret    /* OUT */,
                                        const uint8_t *ciphertext /* IN  */,
                                        const uint8_t *secret_key /* IN  */) {
  return mlkem512_dec(shared_secret, ciphertext, secret_key);
}


int ml_kem_768_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                         uint8_t *secret_key  /* OUT */,
                                         const uint8_t *seed  /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  int res = mlkem768_keypair_derand(public_key, secret_key, seed);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  return res;
}

int ml_kem_768_keypair(uint8_t *public_key /* OUT */,
                           uint8_t *secret_key /* OUT */) {
  boringssl_ensure_ml_kem_self_test();
  int res = mlkem768_keypair(public_key, secret_key);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  return res;
}

int ml_kem_768_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed       /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return mlkem768_enc_derand(ciphertext, shared_secret, public_key, seed);
}

int ml_kem_768_encapsulate(uint8_t *ciphertext       /* OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               const uint8_t *public_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  return mlkem768_enc(ciphertext, shared_secret, public_key);
}

int ml_kem_768_decapsulate(uint8_t *shared_secret    /* OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  return mlkem768_dec(shared_secret, ciphertext, secret_key);
}

int ml_kem_1024_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                          uint8_t *secret_key  /* OUT */,
                                          const uint8_t *seed  /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  int res = mlkem1024_keypair_derand(public_key, secret_key, seed);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  return res;
}

int ml_kem_1024_keypair(uint8_t *public_key /* OUT */,
                            uint8_t *secret_key /* OUT */) {
  boringssl_ensure_ml_kem_self_test();
  int res = mlkem1024_keypair(public_key, secret_key);
#if defined(AWSLC_FIPS)
  /* PCT failure is the only failure condition for key generation. */
  if (res != 0) {
      AWS_LC_FIPS_failure("ML-KEM keygen PCT failed");
  }
#endif
  return res;
}

int ml_kem_1024_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                              uint8_t *shared_secret    /* OUT */,
                                              const uint8_t *public_key /* IN  */,
                                              const uint8_t *seed       /* IN */) {
  boringssl_ensure_ml_kem_self_test();
  return mlkem1024_enc_derand(ciphertext, shared_secret, public_key, seed);
}

int ml_kem_1024_encapsulate(uint8_t *ciphertext       /* OUT */,
                                uint8_t *shared_secret    /* OUT */,
                                const uint8_t *public_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  return mlkem1024_enc(ciphertext, shared_secret, public_key);
}

int ml_kem_1024_decapsulate(uint8_t *shared_secret    /* OUT */,
                                const uint8_t *ciphertext /* IN  */,
                                const uint8_t *secret_key /* IN  */) {
  boringssl_ensure_ml_kem_self_test();
  return mlkem1024_dec(shared_secret, ciphertext, secret_key);
}
