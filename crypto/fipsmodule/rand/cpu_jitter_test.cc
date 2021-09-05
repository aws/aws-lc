/* Copyright (c) 2017, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#if defined(BORINGSSL_FIPS)

#include <gtest/gtest.h>

#include "../../test/test_util.h"
#include "../../../third_party/jitterentropy/jitterentropy.h"

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
  char data0[data_len], data1[data_len];

  // Draw some entropy to check if it works.
  EXPECT_EQ(jent_read_entropy(jitter_ec, data0, data_len), data_len);

  // Draw some entropy with the "safe" API to check if it works.
  EXPECT_EQ(jent_read_entropy_safe(&jitter_ec, data1, data_len), data_len);

  // Basic check that the random data is not equal.
  EXPECT_NE(Bytes(data0), Bytes(data1));

  // Free Jitter instance and initialize a new one with different osr.
  jent_entropy_collector_free(jitter_ec);

  unsigned int osr = 5;
  jitter_ec = jent_entropy_collector_alloc(osr, JENT_FORCE_FIPS);
  EXPECT_EQ(jitter_ec->osr, osr);

  // Verify that the Jitter library version is v3.1.0
  unsigned int jitter_version = 3010000;
  EXPECT_EQ(jitter_version, jent_version());

  jent_entropy_collector_free(jitter_ec);
}

#endif
