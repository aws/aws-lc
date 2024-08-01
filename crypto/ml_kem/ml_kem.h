// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef ML_KEM_H
#define ML_KEM_H

#include <stdint.h>
#include <openssl/base.h>

#define MLKEM512IPD_SHARED_SECRET_LEN (32)
#define MLKEM512IPD_KEYGEN_SEED_LEN   (64)
#define MLKEM512IPD_ENCAPS_SEED_LEN   (32)
#define MLKEM512IPD_PUBLIC_KEY_BYTES  (800)
#define MLKEM512IPD_SECRET_KEY_BYTES  (1632)
#define MLKEM512IPD_CIPHERTEXT_BYTES  (768)

#define MLKEM768IPD_SHARED_SECRET_LEN (32)
#define MLKEM768IPD_KEYGEN_SEED_LEN   (64)
#define MLKEM768IPD_ENCAPS_SEED_LEN   (32)
#define MLKEM768IPD_PUBLIC_KEY_BYTES  (1184)
#define MLKEM768IPD_SECRET_KEY_BYTES  (2400)
#define MLKEM768IPD_CIPHERTEXT_BYTES  (1088)

#define MLKEM1024IPD_SHARED_SECRET_LEN (32)
#define MLKEM1024IPD_KEYGEN_SEED_LEN   (64)
#define MLKEM1024IPD_ENCAPS_SEED_LEN   (32)
#define MLKEM1024IPD_PUBLIC_KEY_BYTES  (1568)
#define MLKEM1024IPD_SECRET_KEY_BYTES  (3168)
#define MLKEM1024IPD_CIPHERTEXT_BYTES  (1568)

int ml_kem_512_ipd_keypair_deterministic(uint8_t *public_key /* OUT */,
                                         uint8_t *secret_key /* OUT */,
                                         const uint8_t *seed /* IN */);

int ml_kem_512_ipd_keypair(uint8_t *public_key /* OUT */,
                           uint8_t *secret_key /* OUT */);

int ml_kem_512_ipd_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed /* IN */);

int ml_kem_512_ipd_encapsulate(uint8_t *ciphertext       /* OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               const uint8_t *public_key /* IN  */);

int ml_kem_512_ipd_decapsulate(uint8_t *shared_secret    /* OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */);

int ml_kem_768_ipd_keypair_deterministic(uint8_t *public_key /* OUT */,
                                         uint8_t *secret_key /* OUT */,
                                         const uint8_t *seed /* IN */);

int ml_kem_768_ipd_keypair(uint8_t *public_key /* OUT */,
                           uint8_t *secret_key /* OUT */);

int ml_kem_768_ipd_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                             uint8_t *shared_secret    /* OUT */,
                                             const uint8_t *public_key /* IN  */,
                                             const uint8_t *seed /* IN */);

int ml_kem_768_ipd_encapsulate(uint8_t *ciphertext       /* OUT */,
                               uint8_t *shared_secret    /* OUT */,
                               const uint8_t *public_key /* IN  */);

int ml_kem_768_ipd_decapsulate(uint8_t *shared_secret    /* OUT */,
                               const uint8_t *ciphertext /* IN  */,
                               const uint8_t *secret_key /* IN  */);

int ml_kem_1024_ipd_keypair_deterministic(uint8_t *public_key /* OUT */,
                                          uint8_t *secret_key /* OUT */,
                                          const uint8_t *seed /* IN */);

int ml_kem_1024_ipd_keypair(uint8_t *public_key /* OUT */,
                            uint8_t *secret_key /* OUT */);

int ml_kem_1024_ipd_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                              uint8_t *shared_secret    /* OUT */,
                                              const uint8_t *public_key /* IN  */,
                                              const uint8_t *seed /* IN */);

int ml_kem_1024_ipd_encapsulate(uint8_t *ciphertext       /* OUT */,
                                uint8_t *shared_secret    /* OUT */,
                                const uint8_t *public_key /* IN  */);

int ml_kem_1024_ipd_decapsulate(uint8_t *shared_secret    /* OUT */,
                                const uint8_t *ciphertext /* IN  */,
                                const uint8_t *secret_key /* IN  */);
#endif // ML_KEM_H
