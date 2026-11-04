// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <string.h>

#include <openssl/crypto.h>

#include "internal.h"
#include "../../../ube/vm_ube_detect.h"

#if !defined(DISABLE_CPU_JITTER_ENTROPY)
#include "../../../../third_party/jitterentropy/jitterentropy-library/jitterentropy.h"
#endif

#define MAX_MULTIPLE_FROM_RNG 16

// We can't easily induce a controllable hardware rng failure, which means the
// retry logic in |rndr_multiple8| and |rdrand_multiple8| can't be exercised by
// calling the real hardware rng. Instead, mock the failures using a fake
// hardware rng function.
struct MockedHwRng {
  // failures is the number of leading calls that must fail.
  size_t failures = 0;
  // bytes_written_on_failure is the number of bytes a failing call writes to
  // the output buffer before failing. RNDR[RS]/RD[SEED|RAND] return 8 bytes and
  // can therefore fail after having written a prefix of the output buffer.
  size_t bytes_written_on_failure = 0;
  // calls is the number of calls observed.
  size_t calls = 0;
};

// kFailureFill is the byte a failing call writes to the output buffer. It must
// differ from |kSuccessFill| to be able to detect a stale prefix left behind by
// a failing call.
static const uint8_t kFailureFill = 0xaa;
// kSuccessFill is the byte a succeeding call writes to the output buffer.
static const uint8_t kSuccessFill = 0x55;

static MockedHwRng mocked_hw_rng;

static int mocked_hw_rng_multiple8(uint8_t *buf, size_t len) {
  mocked_hw_rng.calls += 1;

  if (mocked_hw_rng.calls <= mocked_hw_rng.failures) {
    size_t prefix = mocked_hw_rng.bytes_written_on_failure;
    if (prefix > len) {
      prefix = len;
    }
    memset(buf, kFailureFill, prefix);
    return 0;
  }

  memset(buf, kSuccessFill, len);
  return 1;
}

// TestHwRngRetryLogic exercises the retry logic with |max_attempts| as the
// attempt bound configured for a hardware rng e.g. |RNDR_MAX_ATTEMPTS|.
static void TestHwRngRetryLogic(size_t max_attempts) {
  ASSERT_GT(max_attempts, 0u);

  uint8_t buf[MAX_MULTIPLE_FROM_RNG*8];
  const size_t len = sizeof(buf);

  // Succeeding on the first call executes the hardware rng exactly once.
  mocked_hw_rng = MockedHwRng();
  memset(buf, 0, len);
  ASSERT_TRUE(hw_rng_multiple8_with_retry_FOR_TESTING(
    mocked_hw_rng_multiple8, buf, len, max_attempts));
  EXPECT_EQ(1u, mocked_hw_rng.calls);
  for (size_t i = 0; i < len; i++) {
    EXPECT_EQ(kSuccessFill, buf[i]);
  }

  // Succeeding on the last permitted attempt is still a success and the entire
  // output buffer is written.
  mocked_hw_rng = MockedHwRng();
  mocked_hw_rng.failures = max_attempts - 1;
  memset(buf, 0, len);
  ASSERT_TRUE(hw_rng_multiple8_with_retry_FOR_TESTING(
    mocked_hw_rng_multiple8, buf, len, max_attempts));
  EXPECT_EQ(max_attempts, mocked_hw_rng.calls);
  for (size_t i = 0; i < len; i++) {
    EXPECT_EQ(kSuccessFill, buf[i]);
  }

  // Exhausting the attempt bound is a failure and no further calls are made.
  // The output buffer is not scrubbed, so it can retain what the last failing
  // call wrote; callers must not consume |buf| unless 1 is returned.
  mocked_hw_rng = MockedHwRng();
  mocked_hw_rng.failures = max_attempts + 1;
  mocked_hw_rng.bytes_written_on_failure = len;
  memset(buf, 0, len);
  ASSERT_FALSE(hw_rng_multiple8_with_retry_FOR_TESTING(
    mocked_hw_rng_multiple8, buf, len, max_attempts));
  EXPECT_EQ(max_attempts, mocked_hw_rng.calls);
  for (size_t i = 0; i < len; i++) {
    EXPECT_EQ(kFailureFill, buf[i]);
  }

  // A failing call can leave a prefix of the output buffer written. The
  // succeeding retry must overwrite the entire output buffer. Zeroing |buf|
  // first is what makes the check below meaningful: the preceding cases leave
  // |buf| filled, so without it the check could pass on stale contents.
  if (max_attempts > 1) {
    mocked_hw_rng = MockedHwRng();
    mocked_hw_rng.failures = 1;
    mocked_hw_rng.bytes_written_on_failure = len / 2;
    memset(buf, 0, len);
    ASSERT_TRUE(hw_rng_multiple8_with_retry_FOR_TESTING(
      mocked_hw_rng_multiple8, buf, len, max_attempts));
    EXPECT_EQ(2u, mocked_hw_rng.calls);
    for (size_t i = 0; i < len; i++) {
      EXPECT_EQ(kSuccessFill, buf[i]);
    }
  }

  // Unsupported lengths are rejected without executing the hardware rng.
  for (size_t bad_len : {0, 1, 7, 9, 15}) {
    mocked_hw_rng = MockedHwRng();
    ASSERT_FALSE(hw_rng_multiple8_with_retry_FOR_TESTING(
      mocked_hw_rng_multiple8, buf, bad_len, max_attempts));
    EXPECT_EQ(0u, mocked_hw_rng.calls);
  }
}

TEST(EntropySourceHw, HwRngRetryLogic) {
  // The retry logic is shared between |rndr_multiple8| and |rdrand_multiple8|,
  // but each hardware rng configures its own attempt bound. A bound of 1 is the
  // boundary case where no retry is permitted.
  for (size_t max_attempts : {1, RNDR_MAX_ATTEMPTS, RDRAND_MAX_ATTEMPTS}) {
    SCOPED_TRACE(max_attempts);
    TestHwRngRetryLogic(max_attempts);
  }
}

// In the future this test can be improved by being able to predict whether the
// test is running on hardware that we expect to support RNDR. This will require
// amending the CI with such information.
// For now, simply ensure we exercise all code-paths in the hw rng
// implementations.

TEST(EntropySourceHw, Aarch64) {
  uint8_t buf[MAX_MULTIPLE_FROM_RNG*8] = { 0 } ;

#if !defined(OPENSSL_AARCH64) || defined(OPENSSL_NO_ASM)
  ASSERT_FALSE(have_hw_rng_aarch64_for_testing());
  ASSERT_FALSE(rndr_multiple8(buf, 0));
  ASSERT_FALSE(rndr_multiple8(buf, 8));
#else
  if (have_hw_rng_aarch64_for_testing() != 1) {
    GTEST_SKIP() << "Compiled for Arm64, but Aarch64 hw rng is not available in run-time";
  }

  // Extracting 0 bytes is never supported.
  ASSERT_FALSE(rndr_multiple8(buf, 0));

  // Multiples of 8 allowed.
  for (size_t i = 8; i <= sizeof(buf); i += 8) {
    ASSERT_TRUE(rndr_multiple8(buf, i));
  }

  // Must be multiples of 8.
  for (size_t i : {1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15}) {
    ASSERT_FALSE(rndr_multiple8(buf, i));
  }
#endif
}

TEST(EntropySourceHw, x86_64) {
  uint8_t buf[MAX_MULTIPLE_FROM_RNG*8] = { 0 } ;

#if !defined(OPENSSL_X86_64) || defined(OPENSSL_NO_ASM)
  ASSERT_FALSE(have_hw_rng_x86_64_for_testing());
  ASSERT_FALSE(rdrand_multiple8(buf, 0));
  ASSERT_FALSE(rdrand_multiple8(buf, 8));
#else
  if (have_hw_rng_x86_64_for_testing() != 1) {
    GTEST_SKIP() << "Compiled for x86_64, but x86_64 hw rng is not available in run-time";
  }

  // Extracting 0 bytes is never supported.
  ASSERT_FALSE(rdrand_multiple8(buf, 0));

  // Multiples of 8 allowed.
  for (size_t i = 8; i <= sizeof(buf); i += 8) {
    ASSERT_TRUE(rdrand_multiple8(buf, i));
  }

  // Must be multiples of 8.
  for (size_t i : {1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15}) {
    ASSERT_FALSE(rdrand_multiple8(buf, i));
  }
#endif
}

TEST(EntropySources, Configuration) {
  // VM UBE and explicit opt-out take precedence over either tree policy.
#if (defined(AWSLC_VM_UBE_TESTING) && defined(OPENSSL_LINUX)) || \
    defined(DISABLE_CPU_JITTER_ENTROPY)
  const int expected_entropy_source_id = OPT_OUT_CPU_JITTER_ENTROPY_SOURCE;
#else
#if defined(BORINGSSL_FIPS)
  int expected_entropy_source_id = TREE_DRBG_JITTER_ENTROPY_SOURCE;
#else
  int expected_entropy_source_id = TREE_DRBG_JITTER_WITH_OS_FALLBACK_ENTROPY_SOURCE;
#endif
  if (CRYPTO_get_vm_ube_supported()) {
    expected_entropy_source_id = OPT_OUT_CPU_JITTER_ENTROPY_SOURCE;
  }
#endif

  const int selected_id = get_entropy_source_method_id_FOR_TESTING();
  EXPECT_EQ(expected_entropy_source_id, selected_id);
  uint8_t buf[1];
  ASSERT_TRUE(RAND_bytes(buf, sizeof(buf)));
  EXPECT_EQ(selected_id, get_entropy_source_method_id_FOR_TESTING());

  if (selected_id == OPT_OUT_CPU_JITTER_ENTROPY_SOURCE) {
    EXPECT_EQ(0, FIPS_is_entropy_cpu_jitter());
  } else if (FIPS_mode() == 1) {
    EXPECT_EQ(1, FIPS_is_entropy_cpu_jitter());
  }
}

#if !defined(DISABLE_CPU_JITTER_ENTROPY)

// The following tests set health test state directly on a real Jitter Entropy
// instance, so they depend on the vendored library's internals. Mocked failure
// injection is in tree_drbg_jitter_entropy_isolated_test.cc.

TEST(EntropySourceTreeJitter, RootSeedIntermittentHealthFailure) {
  struct rand_data *jitter_ec = jent_entropy_collector_alloc(0, JENT_FORCE_FIPS);
  ASSERT_TRUE(jitter_ec);
  const unsigned int osr = jitter_ec->osr;

  // Inject an intermittent APT failure at the end of its window. The safe
  // reader carries the APT count over, so a mid-window injection could reach
  // the permanent cutoff on a coarse timer and make the test host-dependent.
  jitter_ec->apt_base_set = 1;
  jitter_ec->apt_count = 0;
  jitter_ec->apt_observations = JENT_APT_WINDOW_SIZE - 1;
  jitter_ec->health_failure = JENT_APT_FAILURE;

  uint8_t seed[CTR_DRBG_ENTROPY_LEN];
  tree_jitter_get_root_seed_FOR_TESTING(&jitter_ec, seed);
#if defined(BORINGSSL_FIPS)
  // FIPS builds retry with a new instance at the same oversampling rate.
  ASSERT_TRUE(jitter_ec);
  EXPECT_EQ(osr, jitter_ec->osr);
#else
  // Non-FIPS builds retry at a higher rate. On a coarse timer the retry can
  // need several rates, or fall back to OS entropy.
  if (jitter_ec == nullptr) {
    GTEST_SKIP() << "Jitter Entropy fell back to OS entropy on this host";
  }
  EXPECT_GT(jitter_ec->osr, osr);
#endif
  EXPECT_EQ(0u, jitter_ec->health_failure);

  jent_entropy_collector_free(jitter_ec);
}

#if !defined(BORINGSSL_FIPS)
TEST(EntropySourceTreeJitter, RootSeedPermanentHealthFailure) {
  struct rand_data *jitter_ec = jent_entropy_collector_alloc(0, JENT_FORCE_FIPS);
  ASSERT_TRUE(jitter_ec);
  jitter_ec->health_failure = JENT_APT_FAILURE_PERMANENT;

  // The safe reader reports a permanent failure without freeing the collector,
  // so the root seed source must discard it and use OS entropy instead.
  uint8_t seed[CTR_DRBG_ENTROPY_LEN] = {0};
  const uint8_t zeros[CTR_DRBG_ENTROPY_LEN] = {0};
  tree_jitter_get_root_seed_FOR_TESTING(&jitter_ec, seed);
  EXPECT_EQ(nullptr, jitter_ec);
  EXPECT_NE(0, memcmp(seed, zeros, sizeof(seed)));
}
#endif

#endif // !defined(DISABLE_CPU_JITTER_ENTROPY)
