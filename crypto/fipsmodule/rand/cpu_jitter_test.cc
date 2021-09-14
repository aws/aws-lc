// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#if defined(BORINGSSL_FIPS)

#include <gtest/gtest.h>

#include "../../test/test_util.h"
#include "../../../third_party/jitterentropy/jitterentropy.h"

BSSL_NAMESPACE_BEGIN
BORINGSSL_MAKE_DELETER(rand_data, jent_entropy_collector_free)
BSSL_NAMESPACE_END

TEST(CPUJitterEntropyTest, Basic) {

  rand_data *jitter_ec = nullptr;

  // Allocate Jitter instance with default oversampling rate.
  jitter_ec = jent_entropy_collector_alloc(0, JENT_FORCE_FIPS);

  // Check that the instance is properly allocated and initialized.
  EXPECT_NE(jitter_ec, nullptr);

  // Check that the default oversampling rate is 3 as expected.
  unsigned int default_osr = 3;
  EXPECT_EQ(jitter_ec->osr, default_osr);

  const ssize_t data_len = 48;
  uint8_t data0[data_len], data1[data_len];

  // Draw some entropy to check if it works.
  EXPECT_EQ(jent_read_entropy(jitter_ec, (char*) data0, data_len), data_len);

  // Draw some entropy with the "safe" API to check if it works.
  EXPECT_EQ(
      jent_read_entropy_safe(&jitter_ec, (char*) data1, data_len), data_len);

  // Basic check that the random data is not equal.
  EXPECT_NE(Bytes(data0), Bytes(data1));

  // Free Jitter instance and initialize a new one with different osr.
  jent_entropy_collector_free(jitter_ec);

  unsigned int osr = 5;
  jitter_ec = jent_entropy_collector_alloc(osr, JENT_FORCE_FIPS);
  EXPECT_EQ(jitter_ec->osr, osr);

  // Verify that the Jitter library version is v3.1.0.
  unsigned int jitter_version = 3010000;
  EXPECT_EQ(jitter_version, jent_version());
}

#endif
