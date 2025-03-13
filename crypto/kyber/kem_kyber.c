// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "../evp_extra/internal.h"
#include "../fipsmodule/evp/internal.h"
#include "../fipsmodule/kem/internal.h"
#include "kem_kyber.h"
#include "pqcrystals_kyber_ref_common/api.h"

// Legacy KEM drivers for kyber.
// The reference pqcrystals_kyber* inverts our usual convention of success (1)
// and fails (0). Define wrappers to handle that.

static int kyber512r3_keygen_deterministic(uint8_t *public_key,
                                           size_t *public_len,
                                           uint8_t *secret_key,
                                           size_t *secret_len,
                                           const uint8_t *seed) {
  return pqcrystals_kyber512_ref_keypair_derand(public_key, secret_key, seed) == 0;
}

static int kyber512r3_keygen(uint8_t *public_key,
                             size_t *public_len,
                             uint8_t *secret_key,
                             size_t *secret_len) {
  return pqcrystals_kyber512_ref_keypair(public_key, secret_key) == 0;
}

static int kyber512r3_encaps_deterministic(uint8_t *ciphertext,
                                           size_t *ciphertext_len,
                                           uint8_t *shared_secret,
                                           size_t *shared_secret_len,
                                           const uint8_t *public_key,
                                           const uint8_t *seed) {
  return pqcrystals_kyber512_ref_enc_derand(ciphertext, shared_secret, public_key, seed) == 0;
}

static int kyber512r3_encaps(uint8_t *ciphertext,
                             size_t *ciphertext_len,
                             uint8_t *shared_secret,
                             size_t *shared_secret_len,
                             const uint8_t *public_key) {
  return pqcrystals_kyber512_ref_enc(ciphertext, shared_secret, public_key) == 0;
}

static int kyber512r3_decaps(uint8_t *shared_secret,
                             size_t *shared_secret_len,
                             const uint8_t *ciphertext,
                             const uint8_t *secret_key) {
  return pqcrystals_kyber512_ref_dec(shared_secret, ciphertext, secret_key) == 0;
}

static const KEM_METHOD kem_kyber512r3_method = {
  kyber512r3_keygen_deterministic,
  kyber512r3_keygen,
  kyber512r3_encaps_deterministic,
  kyber512r3_encaps,
  kyber512r3_decaps,
};

static int kyber768r3_keygen_deterministic(uint8_t *public_key,
                                           size_t *public_len,
                                           uint8_t *secret_key,
                                           size_t *secret_len,
                                           const uint8_t *seed) {
  return pqcrystals_kyber768_ref_keypair_derand(public_key, secret_key, seed) == 0;
}

static int kyber768r3_keygen(uint8_t *public_key,
                             size_t *public_len,
                             uint8_t *secret_key,
                             size_t *secret_len) {
  return pqcrystals_kyber768_ref_keypair(public_key, secret_key) == 0;
}

static int kyber768r3_encaps_deterministic(uint8_t *ciphertext,
                                           size_t *ciphertext_len,
                                           uint8_t *shared_secret,
                                           size_t *shared_secret_len,
                                           const uint8_t *public_key,
                                           const uint8_t *seed) {
  return pqcrystals_kyber768_ref_enc_derand(ciphertext, shared_secret, public_key, seed) == 0;
}

static int kyber768r3_encaps(uint8_t *ciphertext,
                             size_t *ciphertext_len,
                             uint8_t *shared_secret,
                             size_t *shared_secret_len,
                             const uint8_t *public_key) {
  return pqcrystals_kyber768_ref_enc(ciphertext, shared_secret, public_key) == 0;
}

static int kyber768r3_decaps(uint8_t *shared_secret,
                             size_t *shared_secret_len,
                             const uint8_t *ciphertext,
                             const uint8_t *secret_key) {
  return pqcrystals_kyber768_ref_dec(shared_secret, ciphertext, secret_key) == 0;
}

static const KEM_METHOD kem_kyber768r3_method = {
  kyber768r3_keygen_deterministic,
  kyber768r3_keygen,
  kyber768r3_encaps_deterministic,
  kyber768r3_encaps,
  kyber768r3_decaps,
};

static int kyber1024r3_keygen_deterministic(uint8_t *public_key,
                                            size_t *public_len,
                                            uint8_t *secret_key,
                                            size_t *secret_len,
                                            const uint8_t *seed) {
  return pqcrystals_kyber1024_ref_keypair_derand(public_key, secret_key, seed) == 0;
}

static int kyber1024r3_keygen(uint8_t *public_key,
                              size_t *public_len,
                              uint8_t *secret_key,
                              size_t *secret_len) {
  return pqcrystals_kyber1024_ref_keypair(public_key, secret_key) == 0;
}

static int kyber1024r3_encaps_deterministic(uint8_t *ciphertext,
                                            size_t *ciphertext_len,
                                            uint8_t *shared_secret,
                                            size_t *shared_secret_len,
                                            const uint8_t *public_key,
                                            const uint8_t *seed) {
  return pqcrystals_kyber1024_ref_enc_derand(ciphertext, shared_secret, public_key, seed) == 0;
}

static int kyber1024r3_encaps(uint8_t *ciphertext,
                              size_t *ciphertext_len,
                              uint8_t *shared_secret,
                              size_t *shared_secret_len,
                              const uint8_t *public_key) {
  return pqcrystals_kyber1024_ref_enc(ciphertext, shared_secret, public_key) == 0;
}

static int kyber1024r3_decaps(uint8_t *shared_secret,
                              size_t *shared_secret_len,
                              const uint8_t *ciphertext,
                              const uint8_t *secret_key) {
  return pqcrystals_kyber1024_ref_dec(shared_secret, ciphertext, secret_key) == 0;
}

static const KEM_METHOD kem_kyber1024r3_method = {
  kyber1024r3_keygen_deterministic,
  kyber1024r3_keygen,
  kyber1024r3_encaps_deterministic,
  kyber1024r3_encaps,
  kyber1024r3_decaps,
};

// The KEM parameters listed below are taken from corresponding specifications.
// These are legacy KEMs before the NIST PQC project finalized its
// recommendations.
//
// Kyber:
// Implemented as specified in Round 3 of the NIST PQC project
// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210804.pdf.
// OIDs will maintain placeholder values until implementation is deleted.

static const uint8_t kOIDKyber512r3[]   = {0xff, 0xff, 0xff, 0xff};
static const uint8_t kOIDKyber768r3[]   = {0xff, 0xff, 0xff, 0xff};
static const uint8_t kOIDKyber1024r3[]  = {0xff, 0xff, 0xff, 0xff};

static const KEM legacy_kem_kyber512_r3 = {
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
};
const KEM *get_legacy_kem_kyber512_r3(void) {
  return &legacy_kem_kyber512_r3;
}

static const KEM legacy_kem_kyber768_r3 = {
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
};
const KEM *get_legacy_kem_kyber768_r3(void) {
  return &legacy_kem_kyber768_r3;
}

static const KEM legacy_kem_kyber1024_r3 = {
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
};
const KEM *get_legacy_kem_kyber1024_r3(void) {
  return &legacy_kem_kyber1024_r3;
}
