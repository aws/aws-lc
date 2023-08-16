// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef KEM_KYBER_H
#define KEM_KYBER_H

#include <stddef.h>
#include <stdint.h>
#include <openssl/base.h>
#include <openssl/evp.h>

int kyber512r3_keypair(uint8_t *public_key /* OUT */,
                     uint8_t *secret_key /* OUT */);

int kyber512r3_encapsulate(uint8_t *ciphertext       /* OUT */,
                         uint8_t *shared_secret    /* OUT */,
                         const uint8_t *public_key /* IN  */);

int kyber512r3_decapsulate(uint8_t *shared_secret    /* OUT */,
                         const uint8_t *ciphertext /* IN  */,
                         const uint8_t *secret_key /* IN  */);

int kyber768r3_keypair(uint8_t *public_key /* OUT */,
                     uint8_t *secret_key /* OUT */);

int kyber768r3_encapsulate(uint8_t *ciphertext       /* OUT */,
                         uint8_t *shared_secret    /* OUT */,
                         const uint8_t *public_key /* IN  */);

int kyber768r3_decapsulate(uint8_t *shared_secret    /* OUT */,
                         const uint8_t *ciphertext /* IN  */,
                         const uint8_t *secret_key /* IN  */);

int kyber1024r3_keypair(uint8_t *public_key /* OUT */,
                      uint8_t *secret_key /* OUT */);

int kyber1024r3_encapsulate(uint8_t *ciphertext       /* OUT */,
                          uint8_t *shared_secret    /* OUT */,
                          const uint8_t *public_key /* IN  */);

int kyber1024r3_decapsulate(uint8_t *shared_secret    /* OUT */,
                          const uint8_t *ciphertext /* IN  */,
                          const uint8_t *secret_key /* IN  */);

#endif

