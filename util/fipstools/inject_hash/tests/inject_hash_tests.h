// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include "../common.h"

// TODO: change this based on platform, we only care about Apple for now
#define GOOD_LIB_NAME "test_libs/libgood_lib.dylib"
#define BAD_HASH_LIB_NAME "test_libs/libbad_hash_lib.dylib"

class InjectHashTestFixture : public ::testing::Test {
protected:
    static constexpr char const *good_lib_filename = GOOD_LIB_NAME;
    static constexpr char const *bad_hash_lib_filename = BAD_HASH_LIB_NAME;
};
