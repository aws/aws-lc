// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/nid.h>

#include "../fipsmodule/delocate.h"
#include "../fipsmodule/kem/internal.h"
#include "../internal.h"
#include "internal.h"
#include "../kyber/kem_kyber.h"
#include "../fipsmodule/ml_kem/ml_kem.h"


// The KEM parameters listed below are taken from corresponding specifications.
// These are legacy KEMs before the NIST PQC project finalized its
// recommendations.
//
// Kyber: - https://pq-crystals.org/kyber/data/kyber-specification-round3-20210804.pdf
//        - Implemented as specified in Round 3 of NIST PQC project.

#define AWSLC_NUM_LEGACY_KEMS 3

static const uint8_t kOIDKyber512r3[]   = {0xff, 0xff, 0xff, 0xff};
static const uint8_t kOIDKyber768r3[]   = {0xff, 0xff, 0xff, 0xff};
static const uint8_t kOIDKyber1024r3[]  = {0xff, 0xff, 0xff, 0xff};

const KEM legacy_kems[AWSLC_NUM_LEGACY_KEMS] = {
  {
    NID_KYBER512_R3,                // kem.nid
    kOIDKyber512r3,                 // kem.oid
    sizeof(kOIDKyber512r3),         // kem.oid_len
    "Kyber512 Round-3",             // kem.comment
    KYBER512_R3_PUBLIC_KEY_BYTES,   // kem.public_key_len
    KYBER512_R3_SECRET_KEY_BYTES,   // kem.secret_key_len
    KYBER512_R3_CIPHERTEXT_BYTES,   // kem.ciphertext_len
    KYBER_R3_SHARED_SECRET_LEN,     // kem.shared_secret_len
    KYBER_R3_KEYGEN_SEED_LEN,       // kem.keygen_seed_len
    KYBER_R3_ENCAPS_SEED_LEN,       // kem.encaps_seed_len
    &kem_kyber512r3_method,         // kem.method
  },
  {
    NID_KYBER768_R3,                // kem.nid
    kOIDKyber768r3,                 // kem.oid
    sizeof(kOIDKyber768r3),         // kem.oid_len
    "Kyber768 Round-3",             // kem.comment
    KYBER768_R3_PUBLIC_KEY_BYTES,   // kem.public_key_len
    KYBER768_R3_SECRET_KEY_BYTES,   // kem.secret_key_len
    KYBER768_R3_CIPHERTEXT_BYTES,   // kem.ciphertext_len
    KYBER_R3_SHARED_SECRET_LEN,     // kem.shared_secret_len
    KYBER_R3_KEYGEN_SEED_LEN,       // kem.keygen_seed_len
    KYBER_R3_ENCAPS_SEED_LEN,       // kem.encaps_seed_len
    &kem_kyber768r3_method,         // kem.method
  },
  {
    NID_KYBER1024_R3,               // kem.nid
    kOIDKyber1024r3,                // kem.oid
    sizeof(kOIDKyber1024r3),        // kem.oid_len
    "Kyber1024 Round-3",            // kem.comment
    KYBER1024_R3_PUBLIC_KEY_BYTES,  // kem.public_key_len
    KYBER1024_R3_SECRET_KEY_BYTES,  // kem.secret_key_len
    KYBER1024_R3_CIPHERTEXT_BYTES,  // kem.ciphertext_len
    KYBER_R3_SHARED_SECRET_LEN,     // kem.shared_secret_len
    KYBER_R3_KEYGEN_SEED_LEN,       // kem.keygen_seed_len
    KYBER_R3_ENCAPS_SEED_LEN,       // kem.encaps_seed_len
    &kem_kyber1024r3_method,        // kem.method
  },
};

const KEM *get_legacy_kems(void) {
  return legacy_kems;
}
