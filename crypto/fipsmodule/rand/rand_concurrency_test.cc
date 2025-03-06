// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <openssl/ctrdrbg.h>
#include <openssl/mem.h>
#include <openssl/rand.h>

#include "entropy/internal.h"
#include "internal.h"

#include "../../test/test_util.h"

class randConcurrencyTest : public::testing::Test {
  private:
    static thread_local size_t initializeCount;
    static thread_local size_t zeroizeThreadCount;
    static thread_local size_t freeThreadCount;
    static thread_local size_t getSeedCount;
    static thread_local size_t getExtraEntropyCount;
    static thread_local size_t getPredictionResistanceCount;

    static thread_local size_t cachedInitializeCount;
    static thread_local size_t cachedZeroizeThreadCount;
    static thread_local size_t cachedFreeThreadCount;
    static thread_local size_t cachedGetSeedCount;
    static thread_local size_t cachedGetExtraEntropyCount;
    static thread_local size_t cachedGetPredictionResistanceCount;

  protected:
    static int overrideInitialize(struct entropy_source_t *entropy_source) {
      initializeCount++;
      fprintf(stderr, "overrideInitialize\n");
      return 1;
    }

    static size_t getInitializeCount(void) {
      return initializeCount;
    }

    static void overrideZeroizeThread(struct entropy_source_t *entropy_source) {
      zeroizeThreadCount++;
      fprintf(stderr, "overrideZeroizeThread\n");
    }

    static size_t getZeroizeThreadCount(void) {
      return zeroizeThreadCount;
    }

    static void overrideFreeThread(struct entropy_source_t *entropy_source) {
      freeThreadCount++;
      fprintf(stderr, "overrideFreeThread\n");
    }

    static size_t getFreeThreadCount(void) {
      return freeThreadCount;
    }

    static int overrideGetSeed(const struct entropy_source_t *entropy_source,
      uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
      getSeedCount++;
      fprintf(stderr, "overrideGetSeed\n");
      return 1;
    }

    static size_t getGetSeedCount(void) {
      return getSeedCount;
    }

    static int overrideGetExtraEntropy(const struct entropy_source_t *entropy_source,
      uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
      getExtraEntropyCount++;
      fprintf(stderr, "overrideGetExtraEntropy\n");
      return 1;
    }

    static size_t getGetExtraEntropyCount(void) {
      return getExtraEntropyCount;
    }

    static int overrideGetPredictionResistance(
      const struct entropy_source_t *entropy_source,
      uint8_t seed[RAND_PRED_RESISTANCE_LEN]) {
      getPredictionResistanceCount++;
      fprintf(stderr, "overrideGetPredictionResistance\n");
      return 1;
    }

    static size_t getGetPredictionResistanceCount(void) {
      return getPredictionResistanceCount;
    }

    static void cacheAssertReseed(void) {
      cachedGetSeedCount = getGetSeedCount();
      cachedGetExtraEntropyCount = getGetExtraEntropyCount();
    }

    static bool assertReseed(size_t expectedCount) {
      if (cachedGetSeedCount + expectedCount != getGetSeedCount() ||
          cachedGetExtraEntropyCount + expectedCount != getGetExtraEntropyCount()) {
        fprintf(stderr, "cached Seed count = %zu\n", cachedGetSeedCount);
        fprintf(stderr, "current Seed count = %zu\n", getGetSeedCount());
        fprintf(stderr, "cached extra entropy count = %zu\n", cachedGetExtraEntropyCount);
        fprintf(stderr, "current extra entropy count = %zu\n", getGetExtraEntropyCount());
        return false;
      }
      return true;
    }

    static bool assertReseed(size_t expectedCount, std::function<int()> func) {
      cacheAssertReseed();
      if (func() != 1) {
        return false;
      }
      return assertReseed(expectedCount);
    }
};

// We can't rely on Google Test executing all test fixtures sequentially. But
// below test fixtures all spawn a child process that will have an independent
// copy of these counters.
thread_local size_t randConcurrencyTest::initializeCount = 0;
thread_local size_t randConcurrencyTest::zeroizeThreadCount = 0;
thread_local size_t randConcurrencyTest::freeThreadCount = 0;
thread_local size_t randConcurrencyTest::getSeedCount = 0;
thread_local size_t randConcurrencyTest::getExtraEntropyCount = 0;
thread_local size_t randConcurrencyTest::getPredictionResistanceCount = 0;

thread_local size_t randConcurrencyTest::cachedInitializeCount = 0;
thread_local size_t randConcurrencyTest::cachedZeroizeThreadCount = 0;
thread_local size_t randConcurrencyTest::cachedFreeThreadCount = 0;
thread_local size_t randConcurrencyTest::cachedGetSeedCount = 0;
thread_local size_t randConcurrencyTest::cachedGetExtraEntropyCount = 0;
thread_local size_t randConcurrencyTest::cachedGetPredictionResistanceCount = 0;

TEST_F(randConcurrencyTest, Basic) {

  EXPECT_EXIT(({

    const struct entropy_source_methods override_entropy_source_methods = {
      &overrideInitialize,
      &overrideZeroizeThread,
      &overrideFreeThread,
      &overrideGetSeed,
      &overrideGetExtraEntropy,
      &overrideGetPredictionResistance
    };
    override_entropy_source_method_FOR_TESTING(&override_entropy_source_methods);

    std::vector<uint8_t> init_buffer(64);
    ASSERT_TRUE(RAND_bytes(init_buffer.data(), init_buffer.size()));

    bool exit_code = forkAndRunTest(
      []() {
        // In child. If fork detection is supported, we expect a reseed.
        // If fork detection is not enabled, we also expect a reseed.
        return assertReseed(1, []() {
          std::vector<uint8_t> outputRand(64);
          if (!RAND_bytes(outputRand.data(), outputRand.size())) {
            fprintf(stderr, "FAIL child\n");
            return false;
          }

          return true;
        });
      },
      []() {
        // In parent. Expect no reseed.
        return assertReseed(0, []() {
          std::vector<uint8_t> outputRand(64);
          if (!RAND_bytes(outputRand.data(), outputRand.size())) {
            fprintf(stderr, "FAIL parent\n");
            return false;
          }

          return true;
        });
      }
    );

    exit(exit_code ? 0 : 1);
  }), ::testing::ExitedWithCode(0), "");

  EXPECT_EXIT(({

    const struct entropy_source_methods override_entropy_source_methods = {
      &overrideInitialize,
      &overrideZeroizeThread,
      &overrideFreeThread,
      &overrideGetSeed,
      &overrideGetExtraEntropy,
      &overrideGetPredictionResistance
    };
    override_entropy_source_method_FOR_TESTING(&override_entropy_source_methods);

    std::vector<uint8_t> init_buffer(64);
    ASSERT_TRUE(RAND_bytes(init_buffer.data(), init_buffer.size()));

    bool exit_code = forkAndRunTest(
      []() {
        // In child. Spawn a number of threads before generating randomness.
        // If fork detection is supported, we expect a reseed in each thread.
        // If fork detection is not enabled, we also expect a reseed in each
        // thread.
        std::function<void(bool*)> threadFund = [](bool *result) {
          *result = assertReseed(1, []() {
            std::vector<uint8_t> outputRand(64);
            if (!RAND_bytes(outputRand.data(), outputRand.size())) {
              fprintf(stderr, "FAIL child\n");
              return false;
            }

            return true;
          });
        };
        return threadTest(8, threadFund);
      },
      []() {
        // In parent. Expect no reseed.
        return assertReseed(0, []() {
          std::vector<uint8_t> outputRand(64);
          if (!RAND_bytes(outputRand.data(), outputRand.size())) {
            fprintf(stderr, "FAIL parent\n");
            return false;
          }

          return true;   
        });
      }
    );

    exit(exit_code ? 0 : 1);
  }), ::testing::ExitedWithCode(0), "");
}
