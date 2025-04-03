// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef ML_KEM_H
#define ML_KEM_H

#include <stdint.h>
#include <openssl/base.h>

#define MLKEM512_SHARED_SECRET_LEN (32)
#define MLKEM512_KEYGEN_SEED_LEN   (64)
#define MLKEM512_ENCAPS_SEED_LEN   (32)
#define MLKEM512_PUBLIC_KEY_BYTES  (800)
#define MLKEM512_SECRET_KEY_BYTES  (1632)
#define MLKEM512_CIPHERTEXT_BYTES  (768)

#define MLKEM768_SHARED_SECRET_LEN (32)
#define MLKEM768_KEYGEN_SEED_LEN   (64)
#define MLKEM768_ENCAPS_SEED_LEN   (32)
#define MLKEM768_PUBLIC_KEY_BYTES  (1184)
#define MLKEM768_SECRET_KEY_BYTES  (2400)
#define MLKEM768_CIPHERTEXT_BYTES  (1088)

#define MLKEM1024_SHARED_SECRET_LEN (32)
#define MLKEM1024_KEYGEN_SEED_LEN   (64)
#define MLKEM1024_ENCAPS_SEED_LEN   (32)
#define MLKEM1024_PUBLIC_KEY_BYTES  (1568)
#define MLKEM1024_SECRET_KEY_BYTES  (3168)
#define MLKEM1024_CIPHERTEXT_BYTES  (1568)

int ml_kem_512_keypair_deterministic(uint8_t *public_key /* OUT */,
                                         uint8_t *secret_key /* OUT */,
                                         const uint8_t *seed /* IN */);

int ml_kem_512_keypair_deterministic_no_self_test(uint8_t *public_key  /* OUT */,
                                                  uint8_t *secret_key  /* OUT */,
                                                  const uint8_t *seed  /* IN */);

int ml_kem_512_keypair(uint8_t *public_key /* OUT */,
                           uint8_t *secret_key /* OUT */);

int ml_kem_512_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed /* IN */);

int ml_kem_512_encapsulate_deterministic_no_self_test(uint8_t *ciphertext       /* OUT */,
                                                      uint8_t *shared_secret    /* OUT */,
                                                      const uint8_t *public_key /* IN  */,
                                                      const uint8_t *seed       /* IN */);

int ml_kem_512_encapsulate(uint8_t *ciphertext       /* OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               const uint8_t *public_key /* IN  */);

int ml_kem_512_decapsulate(uint8_t *shared_secret    /* OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */);

int ml_kem_512_decapsulate_no_self_test(uint8_t *shared_secret    /* OUT */,
                                        const uint8_t *ciphertext /* IN  */,
                                        const uint8_t *secret_key /* IN  */);

int ml_kem_768_keypair_deterministic(uint8_t *public_key /* OUT */,
                                         uint8_t *secret_key /* OUT */,
                                         const uint8_t *seed /* IN */);

int ml_kem_768_keypair_deterministic_no_self_test(uint8_t *public_key  /* OUT */,
                                                  uint8_t *secret_key  /* OUT */,
                                                  const uint8_t *seed  /* IN */);


int ml_kem_768_keypair(uint8_t *public_key /* OUT */,
                           uint8_t *secret_key /* OUT */);

int ml_kem_768_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed /* IN */);

int ml_kem_768_encapsulate_deterministic_no_self_test(uint8_t *ciphertext       /* OUT */,
                                                      uint8_t *shared_secret    /* OUT */,
                                                      const uint8_t *public_key /* IN  */,
                                                      const uint8_t *seed       /* IN */);


int ml_kem_768_encapsulate(uint8_t *ciphertext       /* OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               const uint8_t *public_key /* IN  */);

int ml_kem_768_decapsulate(uint8_t *shared_secret    /* OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */);

int ml_kem_768_decapsulate_no_self_test(uint8_t *shared_secret    /* OUT */,
                                        const uint8_t *ciphertext /* IN  */,
                                        const uint8_t *secret_key /* IN  */);

int ml_kem_1024_keypair_deterministic(uint8_t *public_key /* OUT */,
                                          uint8_t *secret_key /* OUT */,
                                          const uint8_t *seed /* IN */);

int ml_kem_1024_keypair_deterministic_no_self_test(uint8_t *public_key  /* OUT */,
                                                  uint8_t *secret_key  /* OUT */,
                                                  const uint8_t *seed  /* IN */);

int ml_kem_1024_keypair(uint8_t *public_key /* OUT */,
                            uint8_t *secret_key /* OUT */);

int ml_kem_1024_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                              uint8_t *shared_secret    /* OUT */,
                                              const uint8_t *public_key /* IN  */,
                                              const uint8_t *seed /* IN */);

int ml_kem_1024_encapsulate_deterministic_no_self_test(uint8_t *ciphertext       /* OUT */,
                                                      uint8_t *shared_secret    /* OUT */,
                                                      const uint8_t *public_key /* IN  */,
                                                      const uint8_t *seed       /* IN */);


int ml_kem_1024_encapsulate(uint8_t *ciphertext       /* OUT */,
                                uint8_t *shared_secret    /* OUT */,
                                const uint8_t *public_key /* IN  */);

int ml_kem_1024_decapsulate(uint8_t *shared_secret    /* OUT */,
                                const uint8_t *ciphertext /* IN  */,
                                const uint8_t *secret_key /* IN  */);

int ml_kem_1024_decapsulate_no_self_test(uint8_t *shared_secret    /* OUT */,
                                        const uint8_t *ciphertext /* IN  */,
                                        const uint8_t *secret_key /* IN  */);


#endif // ML_KEM_H
