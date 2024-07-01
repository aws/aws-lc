// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef KEM_KYBER_H
#define KEM_KYBER_H

#include <stddef.h>
#include <stdint.h>
#include <openssl/base.h>
#include <openssl/evp.h>

#define KYBER_R3_SHARED_SECRET_LEN 32
#define KYBER_R3_KEYGEN_SEED_LEN 64
#define KYBER_R3_ENCAPS_SEED_LEN 32

#define KYBER512_R3_PUBLIC_KEY_BYTES  800
#define KYBER512_R3_SECRET_KEY_BYTES 1632
#define KYBER512_R3_CIPHERTEXT_BYTES 768

#define KYBER768_R3_PUBLIC_KEY_BYTES  1184
#define KYBER768_R3_SECRET_KEY_BYTES 2400
#define KYBER768_R3_CIPHERTEXT_BYTES 1088

#define KYBER1024_R3_PUBLIC_KEY_BYTES  1568
#define KYBER1024_R3_SECRET_KEY_BYTES 3168
#define KYBER1024_R3_CIPHERTEXT_BYTES 1568

int kyber512r3_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                     uint8_t *secret_key  /* OUT */,
                                     const uint8_t *seed  /* IN */);

int kyber512r3_keypair(uint8_t *public_key /* OUT */,
                     uint8_t *secret_key /* OUT */);

int kyber512r3_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                         uint8_t *shared_secret    /* OUT */,
                                         const uint8_t *public_key /* IN  */,
                                         const uint8_t *seed       /* IN */);

int kyber512r3_encapsulate(uint8_t *ciphertext       /* OUT */,
                         uint8_t *shared_secret    /* OUT */,
                         const uint8_t *public_key /* IN  */);

int kyber512r3_decapsulate(uint8_t *shared_secret    /* OUT */,
                         const uint8_t *ciphertext /* IN  */,
                         const uint8_t *secret_key /* IN  */);

int kyber768r3_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                     uint8_t *secret_key  /* OUT */,
                                     const uint8_t *seed  /* IN */);

int kyber768r3_keypair(uint8_t *public_key /* OUT */,
                     uint8_t *secret_key /* OUT */);

int kyber768r3_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                         uint8_t *shared_secret    /* OUT */,
                                         const uint8_t *public_key /* IN  */,
                                         const uint8_t *seed       /* IN */);

int kyber768r3_encapsulate(uint8_t *ciphertext       /* OUT */,
                         uint8_t *shared_secret    /* OUT */,
                         const uint8_t *public_key /* IN  */);

int kyber768r3_decapsulate(uint8_t *shared_secret    /* OUT */,
                         const uint8_t *ciphertext /* IN  */,
                         const uint8_t *secret_key /* IN  */);

int kyber1024r3_keypair_deterministic(uint8_t *public_key  /* OUT */,
                                      uint8_t *secret_key  /* OUT */,
                                      const uint8_t *seed  /* IN */);

int kyber1024r3_keypair(uint8_t *public_key /* OUT */,
                      uint8_t *secret_key /* OUT */);

int kyber1024r3_encapsulate_deterministic(uint8_t *ciphertext       /* OUT */,
                                          uint8_t *shared_secret    /* OUT */,
                                          const uint8_t *public_key /* IN  */,
                                          const uint8_t *seed       /* IN */);

int kyber1024r3_encapsulate(uint8_t *ciphertext       /* OUT */,
                          uint8_t *shared_secret    /* OUT */,
                          const uint8_t *public_key /* IN  */);

int kyber1024r3_decapsulate(uint8_t *shared_secret    /* OUT */,
                          const uint8_t *ciphertext /* IN  */,
                          const uint8_t *secret_key /* IN  */);

#endif

