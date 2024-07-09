// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>

#include "../fipsmodule/delocate.h"
#include "../internal.h"
#include "internal.h"

#include "../kyber/kem_kyber.h"
#include "../ml_kem/ml_kem.h"

static int kyber512r3_keygen_deterministic(uint8_t *public_key,
                                           uint8_t *secret_key,
                                           const uint8_t *seed) {
  return kyber512r3_keypair_deterministic(public_key, secret_key, seed) == 0;
}

static int kyber512r3_keygen(uint8_t *public_key,
                             uint8_t *secret_key) {
  return kyber512r3_keypair(public_key, secret_key) == 0;
}

static int kyber512r3_encaps_deterministic(uint8_t *ciphertext,
                                           uint8_t *shared_secret,
                                           const uint8_t *public_key,
                                           const uint8_t *seed) {
  return kyber512r3_encapsulate_deterministic(ciphertext, shared_secret, public_key, seed) == 0;
}

static int kyber512r3_encaps(uint8_t *ciphertext,
                             uint8_t *shared_secret,
                             const uint8_t *public_key) {
  return kyber512r3_encapsulate(ciphertext, shared_secret, public_key) == 0;
}

static int kyber512r3_decaps(uint8_t *shared_secret,
                             const uint8_t *ciphertext,
                             const uint8_t *secret_key) {
  return kyber512r3_decapsulate(shared_secret, ciphertext, secret_key) == 0;
}

const KEM_METHOD kem_kyber512r3_method = {
  kyber512r3_keygen_deterministic,
  kyber512r3_keygen,
  kyber512r3_encaps_deterministic,
  kyber512r3_encaps,
  kyber512r3_decaps,
};

static int kyber768r3_keygen_deterministic(uint8_t *public_key,
                                           uint8_t *secret_key,
                                           const uint8_t *seed) {
  return kyber768r3_keypair_deterministic(public_key, secret_key, seed) == 0;
}

static int kyber768r3_keygen(uint8_t *public_key,
                             uint8_t *secret_key) {
  return kyber768r3_keypair(public_key, secret_key) == 0;
}

static int kyber768r3_encaps_deterministic(uint8_t *ciphertext,
                                           uint8_t *shared_secret,
                                           const uint8_t *public_key,
                                           const uint8_t *seed) {
  return kyber768r3_encapsulate_deterministic(ciphertext, shared_secret, public_key, seed) == 0;
}

static int kyber768r3_encaps(uint8_t *ciphertext,
                             uint8_t *shared_secret,
                             const uint8_t *public_key) {
  return kyber768r3_encapsulate(ciphertext, shared_secret, public_key) == 0;
}

static int kyber768r3_decaps(uint8_t *shared_secret,
                             const uint8_t *ciphertext,
                             const uint8_t *secret_key) {
  return kyber768r3_decapsulate(shared_secret, ciphertext, secret_key) == 0;
}

const KEM_METHOD kem_kyber768r3_method = {
  kyber768r3_keygen_deterministic,
  kyber768r3_keygen,
  kyber768r3_encaps_deterministic,
  kyber768r3_encaps,
  kyber768r3_decaps,
};

static int kyber1024r3_keygen_deterministic(uint8_t *public_key,
                                            uint8_t *secret_key,
                                            const uint8_t *seed) {
  return kyber1024r3_keypair_deterministic(public_key, secret_key, seed) == 0;
}

static int kyber1024r3_keygen(uint8_t *public_key,
                              uint8_t *secret_key) {
  return kyber1024r3_keypair(public_key, secret_key) == 0;
}

static int kyber1024r3_encaps_deterministic(uint8_t *ciphertext,
                                            uint8_t *shared_secret,
                                            const uint8_t *public_key,
                                            const uint8_t *seed) {
  return kyber1024r3_encapsulate_deterministic(ciphertext, shared_secret, public_key, seed) == 0;
}

static int kyber1024r3_encaps(uint8_t *ciphertext,
                              uint8_t *shared_secret,
                              const uint8_t *public_key) {
  return kyber1024r3_encapsulate(ciphertext, shared_secret, public_key) == 0;
}

static int kyber1024r3_decaps(uint8_t *shared_secret,
                              const uint8_t *ciphertext,
                              const uint8_t *secret_key) {
  return kyber1024r3_decapsulate(shared_secret, ciphertext, secret_key) == 0;
}

const KEM_METHOD kem_kyber1024r3_method = {
  kyber1024r3_keygen_deterministic,
  kyber1024r3_keygen,
  kyber1024r3_encaps_deterministic,
  kyber1024r3_encaps,
  kyber1024r3_decaps,
};

static int ml_kem_512_ipd_keygen_deterministic(uint8_t *public_key,
                                               uint8_t *secret_key,
                                               const uint8_t *seed) {
  return ml_kem_512_ipd_keypair_deterministic(public_key, secret_key, seed) == 0;
}

static int ml_kem_512_ipd_keygen(uint8_t *public_key,
                             uint8_t *secret_key) {
  return ml_kem_512_ipd_keypair(public_key, secret_key) == 0;
}

static int ml_kem_512_ipd_encaps_deterministic(uint8_t *ciphertext,
                                               uint8_t *shared_secret,
                                               const uint8_t *public_key,
                                               const uint8_t *seed) {
  return ml_kem_512_ipd_encapsulate_deterministic(ciphertext, shared_secret, public_key, seed) == 0;
}

static int ml_kem_512_ipd_encaps(uint8_t *ciphertext,
                             uint8_t *shared_secret,
                             const uint8_t *public_key) {
  return ml_kem_512_ipd_encapsulate(ciphertext, shared_secret, public_key) == 0;
}

static int ml_kem_512_ipd_decaps(uint8_t *shared_secret,
                             const uint8_t *ciphertext,
                             const uint8_t *secret_key) {
  return ml_kem_512_ipd_decapsulate(shared_secret, ciphertext, secret_key) == 0;
}

const KEM_METHOD kem_ml_kem_512_ipd_method = {
  ml_kem_512_ipd_keygen_deterministic,
  ml_kem_512_ipd_keygen,
  ml_kem_512_ipd_encaps_deterministic,
  ml_kem_512_ipd_encaps,
  ml_kem_512_ipd_decaps,
};
