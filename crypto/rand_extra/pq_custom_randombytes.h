/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

#ifndef RANDOMBYTES_H
#define RANDOMBYTES_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <stdint.h>

#include <openssl/base.h>

// WARNING: THIS IMPLEMENTATION IS USED ONLY FOR TESTING PURPOSES.
//          DO NOT USE THESE APIS ON YOUR OWN.

OPENSSL_EXPORT void pq_custom_randombytes_use_deterministic_for_testing(void);

OPENSSL_EXPORT void pq_custom_randombytes_init_for_testing(const uint8_t *seed);

int pq_custom_randombytes(uint8_t *out, size_t num_bytes);

#if defined(__cplusplus)
}
#endif

#endif
