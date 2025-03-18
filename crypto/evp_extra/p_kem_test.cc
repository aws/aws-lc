// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <stdint.h>
#include "../fipsmodule/kem/internal.h"
#include "../fipsmodule/ml_kem/ml_kem.h"
#include "../test/test_util.h"

struct MLKEMKeypairTestVector {
  size_t public_len;
  size_t secret_len;
  const uint8_t *seed;
  const int expected;
  int (*keypair_deterministic)(uint8_t *public_key, size_t *public_len, uint8_t *secret_key, size_t *secret_len, const uint8_t *seed);
  int (*keypair)(uint8_t *public_key, size_t *public_len, uint8_t *secret_key, size_t *secret_len);
};

 struct MLKEMEncapsulateTestVector {
  size_t ciphertext_len;
  size_t shared_secret_len;
  const uint8_t *public_key;
  const uint8_t *seed;
  const int expected;
  int (*encapsulate_deterministic)(uint8_t *ciphertext, size_t *ciphertext_len, unit8_t *shared_secret, size_t *shared_secret_len, const uint8_t *public_key, const uint8_t *seed);
  int (*encapsulate)(uint8_t *ciphertext, size_t *ciphertext_len, uint8_t *shared_secret, size_t *shared_secret_len, const uint8_t *public_key);
};

struct MLKEMDecapsulateTestVector {
  size_t shared_secret_len;
  const uint8_t *ciphertext;
  const uint8_t *secret_key;
  const int expected;
  int (*decapsulate)(uint8_t *shared_secret, size_t *shared_secret_len, const uint8_t *ciphertext, const uint8_t *secret_key);
};

static const uint8_t kKeyGenSeed[MLKEM512_KEYGEN_SEED_LEN] = {
  0xf8, 0x8c, 0xb2, 0x5f, 0x89, 0xa3, 0x55, 0x5f, 0xae, 0xc6, 0x71, 0xa1,
  0xdf, 0xc6, 0xf6, 0x1d, 0x60, 0xd0, 0x62, 0x22, 0x7d, 0x6a, 0x8f, 0xf6,
  0x2b, 0x3c, 0x6d, 0x7b, 0xd6, 0x14, 0x0f, 0x66, 0x24, 0xc0, 0x84, 0xa6,
  0x4d, 0xa7, 0x4c, 0x63, 0x32, 0x7e, 0x11, 0x77, 0x58, 0xaa, 0x33, 0x8a,
  0x02, 0xe4, 0x43, 0x74, 0x10, 0xb8, 0xf9, 0xf2, 0x00, 0x88, 0xa1, 0x29,
  0xc1, 0x68, 0x3d, 0xe7
};

static const struct MLKEMKeypairTestVector keypair512ParameterSet[] = {
  {
    MLKEM512_PUBLIC_KEY_BYTES,
    MLKEM512_SECRET_KEY_BYTES,
    kKeyGenSeed,
    0,
    ml_kem_512_keypair_deterministic,
    ml_kem_512_keypair
  },
  {
    MLKEM512_PUBLIC_KEY_BYTES/2,
    MLKEM512_SECRET_KEY_BYTES,
    kKeyGenSeed,
    1,
    ml_kem_512_keypair_deterministic,
    ml_kem_512_keypair
  },
  {
    MLKEM512_PUBLIC_KEY_BYTES,
    MLKEM512_SECRET_KEY_BYTES/2,
    kKeyGenSeed,
    1,
    ml_kem_512_keypair_deterministic,
    ml_kem_512_keypair
  },
  {
    MLKEM512_PUBLIC_KEY_BYTES/2,
    MLKEM512_SECRET_KEY_BYTES/2,
    kKeyGenSeed,
    1,
    ml_kem_512_keypair_deterministic,
    ml_kem_512_keypair
  },
  {
    MLKEM512_PUBLIC_KEY_BYTES*2,
    MLKEM512_SECRET_KEY_BYTES,
    kKeyGenSeed,
    0,
    ml_kem_512_keypair_deterministic,
    ml_kem_512_keypair
  },
  {
    MLKEM512_PUBLIC_KEY_BYTES,
    MLKEM512_SECRET_KEY_BYTES*2,
    kKeyGenSeed,
    0,
    ml_kem_512_keypair_deterministic,
    ml_kem_512_keypair
  },
  {
    MLKEM512_PUBLIC_KEY_BYTES*2,
    MLKEM512_SECRET_KEY_BYTES*2,
    kKeyGenSeed,
    0,
    ml_kem_512_keypair_deterministic,
    ml_kem_512_keypair
  }
};

class MLKEMKeypairLengthTest : public testing::TestWithParam<MLKEMKeypairTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, MLKEMKeypairLengthTest, testing::ValuesIn(keypair512ParameterSet));

static const struct MLKEMEncapsulateTestVector encapsulateParameterSet[] = {};
static const struct MLKEMDecapsulateTestVector decapsulateParameterSet[] = {};