// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef KEM_KYBER_H
#define KEM_KYBER_H

#include <stddef.h>
#include <stdint.h>
#include <openssl/base.h>
#include <openssl/evp.h>

#include "../fipsmodule/kem/internal.h"

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

const KEM * get_legacy_kem_kyber512_r3(void);
const KEM * get_legacy_kem_kyber768_r3(void);
const KEM * get_legacy_kem_kyber1024_r3(void);

#endif

