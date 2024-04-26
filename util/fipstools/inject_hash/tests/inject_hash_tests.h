// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include "../common.h"

// TODO: change this based on platform, we only care about Apple for now
#define GOODLIB_NAME "test_libs/libgood_lib.dylib"

class InjectHashTestFixture : public ::testing::Test {
protected:
    static constexpr char const *good_lib_filename = GOODLIB_NAME;
};
