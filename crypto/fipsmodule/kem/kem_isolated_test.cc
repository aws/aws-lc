// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This is its own executable because it observes the first ML-KEM operation in
// a process, which any earlier ML-KEM test in the same process would hide.

#include <gtest/gtest.h>

#include <cstring>

#include <openssl/bytestring.h>
#include <openssl/ctrdrbg.h>
#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/rand.h>

#include "../rand/entropy/internal.h"
#include "../../test/test_util.h"

// Use `#if GTEST_HAS_DEATH_TEST` (not `defined()`); some toolchains define it to 0.
#if GTEST_HAS_DEATH_TEST && defined(OPENSSL_THREADS)

// RFC 9935 Appendix C, ML-KEM-512 expandedKey. Copied from p_kem_test.cc.
static const char *kMLKEM512ExpandedPEM =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "JCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+Pw==\n"
    "-----END PRIVATE KEY-----\n";

// |rand_bytes_core| queries the prediction resistance source on every
// |RAND_bytes| call, so counting those queries counts the calls themselves.
// The count is per thread, and the test runs in a fresh thread whose DRBG state
// is created from the overridden entropy source. The sources fill their output
// with fixed bytes: the DRBG output reaches ML-KEM, so leaving it uninitialized
// would trip MemorySanitizer.
static thread_local size_t rand_bytes_calls = 0;

static int overrideInitialize(struct entropy_source_t *) { return 1; }
static void overrideZeroizeThread(struct entropy_source_t *) {}
static void overrideFreeThread(struct entropy_source_t *) {}
static int overrideGetSeed(const struct entropy_source_t *,
                           uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
  memset(seed, 0x01, CTR_DRBG_ENTROPY_LEN);
  return 1;
}
static int overrideGetExtraEntropy(const struct entropy_source_t *,
                                   uint8_t extra[CTR_DRBG_ENTROPY_LEN]) {
  memset(extra, 0x02, CTR_DRBG_ENTROPY_LEN);
  return 1;
}
static int overrideGetPredictionResistance(
    const struct entropy_source_t *,
    uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN]) {
  memset(pred_resistance, 0x03, RAND_PRED_RESISTANCE_LEN);
  rand_bytes_calls++;
  return 1;
}

static const entropy_source_methods kCountingEntropyMethods = {
    &overrideInitialize,
    &overrideZeroizeThread,
    &overrideFreeThread,
    &overrideGetSeed,
    &overrideGetExtraEntropy,
    &overrideGetPredictionResistance,
    OVERRIDDEN_ENTROPY_SOURCE};

// Parses |der| and returns the number of |RAND_bytes| calls the parse made, or
// SIZE_MAX if it failed.
static size_t RandBytesCallsToParse(const std::vector<uint8_t> &der) {
  size_t before = rand_bytes_calls;
  CBS cbs;
  CBS_init(&cbs, der.data(), der.size());
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_parse_private_key(&cbs));
  if (!pkey) {
    return SIZE_MAX;
  }
  return rand_bytes_calls - before;
}

// Parsing an expandedKey runs a pairwise consistency test with deterministic
// coins, so the import itself draws no randomness. In FIPS builds the first
// import in a process also runs the lazy ML-KEM self-test, which must still run
// and whose key-generation KAT does draw randomness; later imports draw none.
TEST(KEMIsolatedTest, ExpandedKeyParseRandomnessColdAndRepeated) {
  if (runtimeEmulationIsIntelSde() && addressSanitizerIsEnabled()) {
    GTEST_SKIP() << "Test not supported under Intel SDE + ASAN";
  }

  uint8_t *der_buf = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(kMLKEM512ExpandedPEM, &der_buf, &der_len));
  const std::vector<uint8_t> der(der_buf, der_buf + der_len);
  OPENSSL_free(der_buf);

  auto testFunc = [&der]() {
    override_entropy_source_method_FOR_TESTING(&kCountingEntropyMethods);

    std::function<void(bool *)> threadFunc = [&der](bool *result) {
      *result = false;

      const size_t cold = RandBytesCallsToParse(der);
      if (cold == SIZE_MAX) {
        fprintf(stderr, "cold expandedKey parse failed\n");
        return;
      }
#if defined(BORINGSSL_FIPS)
      if (cold == 0) {
        fprintf(stderr,
                "cold expandedKey parse drew no randomness, so the lazy "
                "ML-KEM self-test did not run\n");
        return;
      }
#else
      if (cold != 0) {
        fprintf(stderr, "cold expandedKey parse made %zu RAND_bytes calls\n",
                cold);
        return;
      }
#endif

      for (int i = 0; i < 3; i++) {
        const size_t repeated = RandBytesCallsToParse(der);
        if (repeated != 0) {
          fprintf(stderr,
                  "repeated expandedKey parse %d made %zu RAND_bytes calls\n",
                  i, repeated);
          return;
        }
      }

      *result = true;
    };

    exit(threadTest(1, threadFunc) ? 0 : 1);
  };

  EXPECT_EXIT(testFunc(), ::testing::ExitedWithCode(0), "");
}

#endif  // GTEST_HAS_DEATH_TEST && OPENSSL_THREADS
