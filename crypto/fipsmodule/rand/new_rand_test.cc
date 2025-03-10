// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <openssl/ctrdrbg.h>
#include <openssl/mem.h>
#include <openssl/rand.h>

#include "internal.h"

#include "../../ube/internal.h"

#include "../../test/ube_test.h"
#include "../../test/test_util.h"

#include <thread>

#define MAX_REQUEST_SIZE (CTR_DRBG_MAX_GENERATE_LENGTH * 2 + 1)

static const size_t global_request_len = 64;
static const size_t number_of_threads = 8;

static void test_all_exported_functions(size_t request_len, uint8_t *out_buf,
  uint8_t user_pred_res[RAND_PRED_RESISTANCE_LEN]) {
  ASSERT_TRUE(RAND_bytes(out_buf, request_len));
  ASSERT_TRUE(RAND_priv_bytes(out_buf, request_len));
  ASSERT_TRUE(RAND_pseudo_bytes(out_buf, request_len));
  ASSERT_TRUE(RAND_bytes_with_user_prediction_resistance(out_buf, request_len, user_pred_res));
}

class newRandTest : public ubeTest {
 public:
  void SetUp() override {
    ubeTest::SetUp();

    // Ensure randomness generation state is initialized.
    uint8_t *randomness = (uint8_t *) OPENSSL_zalloc(MAX_REQUEST_SIZE);
    bssl::UniquePtr<uint8_t> deleter(randomness);
    uint8_t user_prediction_resistance[RAND_PRED_RESISTANCE_LEN] = {0};
    test_all_exported_functions(global_request_len, randomness, user_prediction_resistance);
 }
};

static void randBasicTests(bool *returnFlag) {
  // Do not use stack arrays for these. For example, Alpine OS has too low
  // default thread stack size limit to accommodate.
  uint8_t *randomness = (uint8_t *) OPENSSL_zalloc(MAX_REQUEST_SIZE);
  bssl::UniquePtr<uint8_t> deleter(randomness);
  uint8_t user_prediction_resistance[RAND_PRED_RESISTANCE_LEN] = {0};

  for (size_t i = 0; i < 65; i++) {
    test_all_exported_functions(i, randomness, user_prediction_resistance);
  }

  for (size_t i : {CTR_DRBG_MAX_GENERATE_LENGTH-1, CTR_DRBG_MAX_GENERATE_LENGTH, CTR_DRBG_MAX_GENERATE_LENGTH + 1, CTR_DRBG_MAX_GENERATE_LENGTH * 2}) {
    test_all_exported_functions(i, randomness, user_prediction_resistance);
  }

  *returnFlag = true;
}

TEST_F(newRandTest, Basic) {
  ASSERT_TRUE(threadTest(number_of_threads, randBasicTests));
}

static void randReseedIntervalUbeIsSupportedTests(bool *returnFlag) {
  uint8_t *randomness = (uint8_t *) OPENSSL_zalloc(CTR_DRBG_MAX_GENERATE_LENGTH * 5 + 1);
  bssl::UniquePtr<uint8_t> deleter(randomness);

  // If in a new thread, this will initialize the state.
  ASSERT_TRUE(RAND_bytes(randomness, global_request_len));

  uint64_t reseed_calls_since_initialization = get_thread_reseed_calls_since_initialization();
  uint64_t generate_calls_since_seed = get_thread_generate_calls_since_seed();

  // First check that we can predict when a reseed happens based on the current
  // number of invoked generate calls. After the loop, we expect to be one
  // invoke generate call from a reseed.
  for(size_t i = 0; i < (kCtrDrbgReseedInterval - generate_calls_since_seed); i++) {
    ASSERT_TRUE(RAND_bytes(randomness, 1));
    ASSERT_EQ(get_thread_reseed_calls_since_initialization(), reseed_calls_since_initialization);
  }
  ASSERT_TRUE(RAND_bytes(randomness, 1));
  ASSERT_EQ(get_thread_reseed_calls_since_initialization(), reseed_calls_since_initialization + 1);
  ASSERT_EQ(get_thread_generate_calls_since_seed(), 1ULL);

  ASSERT_TRUE(RAND_bytes(randomness, 1));
  ASSERT_EQ(get_thread_reseed_calls_since_initialization(), reseed_calls_since_initialization + 1);
  ASSERT_EQ(get_thread_generate_calls_since_seed(), 2ULL);

  // Should be able to perform kCtrDrbgReseedInterval-2 generate calls before a
  // reseed is emitted. Requesting
  // CTR_DRBG_MAX_GENERATE_LENGTH * (kCtrDrbgReseedInterval-2) + 1 would require
  // quite a large buffer. Instead iterate until we need
  // 5 iterations and request 5 * CTR_DRBG_MAX_GENERATE_LENGTH+1, which is a
  // much smaller buffer.
  for(size_t i = 0; i < (kCtrDrbgReseedInterval - 7); i++) {
    ASSERT_TRUE(RAND_bytes(randomness, 1));
    ASSERT_EQ(get_thread_reseed_calls_since_initialization(), reseed_calls_since_initialization + 1);
    ASSERT_EQ(get_thread_generate_calls_since_seed(), 2 + (i + 1));
  }
  ASSERT_EQ(get_thread_generate_calls_since_seed(), kCtrDrbgReseedInterval - 5);
  size_t request_len_new_reseed = CTR_DRBG_MAX_GENERATE_LENGTH * 5 + 1;
  ASSERT_TRUE(RAND_bytes(randomness, request_len_new_reseed));
  ASSERT_EQ(get_thread_reseed_calls_since_initialization(), reseed_calls_since_initialization + 2);
  ASSERT_EQ(get_thread_generate_calls_since_seed(), 1ULL);

  *returnFlag = true;
}

TEST_F(newRandTest, ReseedIntervalWhenUbeIsSupported) {
  if (!UbeIsSupported()) {
    GTEST_SKIP() << "UBE detection is not supported";
  }
  ASSERT_TRUE(threadTest(number_of_threads, randReseedIntervalUbeIsSupportedTests));
}

static void randReseedIntervalUbeNotSupportedTests(bool *returnFlag) {
  uint8_t *randomness = (uint8_t *) OPENSSL_zalloc(CTR_DRBG_MAX_GENERATE_LENGTH);
  bssl::UniquePtr<uint8_t> deleter(randomness);

  // If in a new thread, this will initialize the state.
  ASSERT_TRUE(RAND_bytes(randomness, global_request_len));

  uint64_t generate_calls_since_seed = get_thread_generate_calls_since_seed();
  uint64_t reseed_calls_since_initialization = get_thread_reseed_calls_since_initialization();

  if (kCtrDrbgReseedInterval - generate_calls_since_seed < 2) {
    // Ensure the reseed interval doesn't conflict with logic below.
    ASSERT_TRUE(RAND_bytes(randomness, 1));
    ASSERT_TRUE(RAND_bytes(randomness, 1));
  }

  // Each invocation of the randomness generation induce a reseed due to UBE
  // detection not being supported.
  ASSERT_TRUE(RAND_bytes(randomness, 1));
  ASSERT_EQ(get_thread_generate_calls_since_seed(), 1ULL);
  ASSERT_EQ(get_thread_reseed_calls_since_initialization(), reseed_calls_since_initialization + 1);

  ASSERT_TRUE(RAND_bytes(randomness, 1));
  ASSERT_EQ(get_thread_generate_calls_since_seed(), 1ULL);
  ASSERT_EQ(get_thread_reseed_calls_since_initialization(), reseed_calls_since_initialization + 2);

  *returnFlag = true;
}

TEST_F(newRandTest, ReseedIntervalWhenUbeNotSupported) {

  if (UbeIsSupported()) {
    GTEST_SKIP() << "UBE detection is supported";
  }
  ASSERT_TRUE(threadTest(number_of_threads, randReseedIntervalUbeNotSupportedTests));
}

static void MockedUbeDetection(std::function<void(uint64_t)> set_detection_method_gn) {

  const size_t request_size_one_generate = 10;
  const size_t request_size_two_generate = CTR_DRBG_MAX_GENERATE_LENGTH + 1;
  uint64_t current_reseed_calls = 0;
  uint8_t *randomness = (uint8_t *) OPENSSL_zalloc(CTR_DRBG_MAX_GENERATE_LENGTH * 5 + 1);
  bssl::UniquePtr<uint8_t> deleter(randomness);

  // Make sure things are initialized and at default values. Cache
  // current_reseed_calls last in case RAND_bytes() invokes a reseed.
  set_detection_method_gn(1);
  ASSERT_TRUE(RAND_bytes(randomness, request_size_one_generate));
  current_reseed_calls = get_thread_reseed_calls_since_initialization();

  // Bump fork generation number and expect one reseed. In addition, expect one
  // generate call since request size is less than CTR_DRBG_MAX_GENERATE_LENGTH.
  set_detection_method_gn(2);
  ASSERT_TRUE(RAND_bytes(randomness, request_size_one_generate));
  ASSERT_EQ(get_thread_reseed_calls_since_initialization(), current_reseed_calls + 1ULL);
  ASSERT_EQ(get_thread_generate_calls_since_seed(), 1ULL);

  // Bump fork generation number again and expect one reseed. In addition,
  // expect two generate call since request size is higher than
  // CTR_DRBG_MAX_GENERATE_LENGTH.
  set_detection_method_gn(3);
  ASSERT_TRUE(RAND_bytes(randomness, request_size_two_generate));
  ASSERT_EQ(get_thread_reseed_calls_since_initialization(), current_reseed_calls + 2ULL);
  ASSERT_EQ(get_thread_generate_calls_since_seed(), 2ULL);
}

TEST_F(newRandTest, UbeDetectionMocked) {

  allowMockedUbe();

  MockedUbeDetection(
    [](uint64_t gn) {
      set_fork_generation_number_FOR_TESTING(gn);
    }
  );

  MockedUbeDetection(
    [](uint64_t gn) {
      set_snapsafe_generation_number_FOR_TESTING(static_cast<uint32_t>(gn));
    }
  );
}
