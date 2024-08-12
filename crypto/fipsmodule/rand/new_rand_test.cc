// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <openssl/ctrdrbg.h>

#include "new_rand_internal.h"


// TODO
// Remove when promoting to default
#if !defined(BORINGSSL_PREFIX)

#define COMPILATION_UNIT_NR_PREFIX
#include "new_rand_prefix.h"

#define MAX_REQUEST_SIZE (CTR_DRBG_MAX_GENERATE_LENGTH * 2 + 1)

TEST(NewRand, Basic) {

  uint8_t randomness[MAX_REQUEST_SIZE] = {0};
  uint8_t user_personalization_string[RAND_PRED_RESISTANCE_LEN] = {0};

  for (size_t i = 0; i < 65; i++) {
    ASSERT_TRUE(RAND_bytes(randomness, i));
    ASSERT_TRUE(RAND_priv_bytes(randomness, i));
    ASSERT_TRUE(RAND_pseudo_bytes(randomness, i));
    ASSERT_TRUE(RAND_bytes_with_additional_data(randomness, i, user_personalization_string));
    ASSERT_TRUE(RAND_bytes_with_user_prediction_resistance(randomness, i, user_personalization_string));
  }

  for (size_t i : {CTR_DRBG_MAX_GENERATE_LENGTH-1, CTR_DRBG_MAX_GENERATE_LENGTH, CTR_DRBG_MAX_GENERATE_LENGTH + 1, CTR_DRBG_MAX_GENERATE_LENGTH * 2}) {
    ASSERT_TRUE(RAND_bytes(randomness, i));
    ASSERT_TRUE(RAND_priv_bytes(randomness, i));
    ASSERT_TRUE(RAND_pseudo_bytes(randomness, i));
    ASSERT_TRUE(RAND_bytes_with_additional_data(randomness, i, user_personalization_string));
    ASSERT_TRUE(RAND_bytes_with_user_prediction_resistance(randomness, i, user_personalization_string));    
  }
}


#endif
