// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <openssl/ctrdrbg.h>
#include <openssl/mem.h>
#include <openssl/rand.h>

#include "entropy/internal.h"
#include "internal.h"
#include "../../ube/internal.h"

#include "../../test/ube_test.h"
#include "../../test/test_util.h"

static const size_t request_len = 64;
static const size_t number_of_threads = 8;

static thread_local size_t initialize_count = 0;
static thread_local size_t zeroize_thread_count = 0;
static thread_local size_t free_thread_count = 0;
static thread_local size_t get_seed_count = 0;
static thread_local size_t get_extra_entropy_count = 0;
static thread_local size_t get_prediction_resistance_count = 0;

static thread_local size_t cached_get_seed_count = 0;
static thread_local size_t cached_get_extra_entropy_count = 0;

static entropy_source_methods entropy_methods{
  nullptr,  // initialize
  nullptr,  // zeroize_thread
  nullptr,  // free_thread
  nullptr,  // get_seed
  nullptr,  // get_extra_entropy
  nullptr   // get_prediction_resistance
};

static int overrideInitialize(struct entropy_source_t *entropy_source) {
  initialize_count++;
  return 1;
}

static void overrideZeroizeThread(struct entropy_source_t *entropy_source) {
  zeroize_thread_count++;
}

static void overrideFreeThread(struct entropy_source_t *entropy_source) {
  free_thread_count++;
}

static int overrideGetSeed(const struct entropy_source_t *entropy_source,
  uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
  get_seed_count++;
  return 1;
}

static int overrideGetExtraEntropy(const struct entropy_source_t *entropy_source,
  uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
  get_extra_entropy_count++;
  return 1;
}

static int overrideGetPredictionResistance(
  const struct entropy_source_t *entropy_source,
  uint8_t seed[RAND_PRED_RESISTANCE_LEN]) {
  get_prediction_resistance_count++;
  return 1;
}

static void cacheAssertReseed() {
  cached_get_seed_count = get_seed_count;
  cached_get_extra_entropy_count = get_extra_entropy_count;
}

static bool assertReseed(size_t expected_count) {
  if (cached_get_seed_count + expected_count != get_seed_count ||
      cached_get_extra_entropy_count + expected_count != get_extra_entropy_count) {
    std::cerr << "Reseed count mismatch:\n"
              << "  Seed count: expected=" << (cached_get_seed_count + expected_count) 
              << ", actual=" << get_seed_count << '\n'
              << "  Extra entropy count: expected=" << (cached_get_extra_entropy_count + expected_count)
              << ", actual=" << get_extra_entropy_count << '\n';
    return false;
  }
  return true;
}

static bool assertReseed(size_t expected_count, std::function<int()> func) {
  cacheAssertReseed();
  if (func() != 1) {
    return false;
  }
  return assertReseed(expected_count);
}

static void overrideEntropySourceMethodsCount() {
  entropy_methods = {
    &overrideInitialize,
    &overrideZeroizeThread,
    &overrideFreeThread,
    &overrideGetSeed,
    &overrideGetExtraEntropy,
    &overrideGetPredictionResistance
  };
  override_entropy_source_method_FOR_TESTING(&entropy_methods);
}

class randConcurrencyTest : public::testing::Test {
  private:
    UbeBase ube_base_;

  protected:
    void SetUp() override {
      ube_base_.SetUp();
    }

    void TearDown() override {
      ube_base_.TearDown();
    }

    bool UbeIsSupported() const {
      return ube_base_.UbeIsSupported();
    }

    void allowMockedUbe() const {
      ube_base_.allowMockedUbe();
    }
};

static bool generateRandomness(size_t req_Len, const char *error_text = "Failed") {
  std::vector<uint8_t> output_rand(req_Len);
  if (!RAND_bytes(output_rand.data(), output_rand.size())) {
    std::cerr << error_text << '\n';
    return false;
  }
  return true;
}

static bool generateRandomnessChild(void) {
  return generateRandomness(request_len, "Failed in child");
}

static bool generateRandomnessParent(void) {
  return generateRandomness(request_len, "Failed in parent");
}

TEST_F(randConcurrencyTest, BasicThread) {

  // Test reseeds are observed when spawning new threads.
  auto testFunc = [this]() {

    // Setup entropy source method override.
    overrideEntropySourceMethodsCount();
    generateRandomness(request_len);

    std::function<void(bool*)> threadFunc = [this](bool *result) {
      // In a fresh thread, we expect a reseed.
      bool test1 = assertReseed(1, []() {
        return generateRandomness(request_len);
      });

      // If UBE detection is not supported, we expect a reseed again. Otherwise,
      // no reseed is expected.
      size_t expect_reseed = 1;
      if (UbeIsSupported()) {
        expect_reseed = 0;
      }
      bool test2 = assertReseed(expect_reseed, []() {
        return generateRandomness(request_len);
      });

      *result = test1 && test2;
    };

    bool exit_code = threadTest(number_of_threads, threadFunc);
    exit(exit_code ? 0 : 1);
  };

  EXPECT_EXIT(testFunc(), ::testing::ExitedWithCode(0), "");
}

#if !defined(OPENSSL_WINDOWS)
TEST_F(randConcurrencyTest, BasicFork) {

  // Test reseed is observed when forking.
  auto testFuncSingleFork = []() {

    // Setup entropy source method override
    overrideEntropySourceMethodsCount();
    generateRandomness(request_len);

    bool exit_code = forkAndRunTest(
      []() {
        // In child. If fork detection is supported, we expect a reseed.
        // If fork detection is not enabled, we also expect a reseed.
        return assertReseed(1, []() {
          return generateRandomnessChild();
        });
      },
      []() {
        // In parent. Expect no reseed.
        return assertReseed(0, []() {
          return generateRandomnessParent();
        });
      }
    );

    exit(exit_code ? 0 : 1);
  };

  EXPECT_EXIT(testFuncSingleFork(), ::testing::ExitedWithCode(0), "");

  // Test reseed is observed when forking and spawning new threads before
  // generating randomness.
  auto testFuncSingleForkThenThread = []() {

    // Setup entropy source method override
    overrideEntropySourceMethodsCount();
    generateRandomness(request_len);

    bool exit_code = forkAndRunTest(
      []() {
        // In child. Spawn a number of threads before generating randomness.
        // If fork detection is supported, we expect a reseed in each thread.
        // If fork detection is not enabled, we also expect a reseed in each
        // thread.
        std::function<void(bool*)> threadFunc = [](bool *result) {
          *result = assertReseed(1, []() {
            return generateRandomnessChild();
          });
        };
        return threadTest(number_of_threads, threadFunc);
      },
      []() {
        // In parent. Expect no reseed.
        return assertReseed(0, []() {
          return generateRandomnessParent();
        });
      }
    );

    exit(exit_code ? 0 : 1);
  };

  EXPECT_EXIT(testFuncSingleForkThenThread(), ::testing::ExitedWithCode(0), "");
}
#endif
