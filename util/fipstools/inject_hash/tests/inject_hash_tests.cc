// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <assert.h>
#include <gtest/gtest.h>
#include <iostream>
#include <string>

#include "../common.h"

// Paths below are based on expected location of library artifacts relative
// to the location of this test executable.
// TODO: change this based on platform, we only care about Apple for now
#define GOOD_LIB_NAME "test_libs/libgood_lib.dylib"
#define BAD_HASH_LIB_NAME "test_libs/libbad_hash_lib.dylib"
#define BAD_MARKER_LIB_NAME "test_libs/libbad_marker_lib.dylib"

class InjectHashTestFixture : public ::testing::Test {
protected:
    const std::string good_lib_filename = GOOD_LIB_NAME;
    const std::string bad_hash_lib_filename = BAD_HASH_LIB_NAME;
    const std::string bad_marker_lib_filename = BAD_MARKER_LIB_NAME;
};

TEST_F(InjectHashTestFixture, TestGoodLib) {
    std::unique_ptr<uint8_t> object_bytes(nullptr);
    size_t object_bytes_size;

    uint8_t *object_bytes_ptr = object_bytes.get();

    ASSERT_EQ(1, inject_hash_no_write(good_lib_filename.c_str(), 1, &object_bytes_ptr, &object_bytes_size));
}

TEST_F(InjectHashTestFixture, TestBadHashLib) {
    std::unique_ptr<uint8_t> object_bytes(nullptr);
    size_t object_bytes_size;

    uint8_t *object_bytes_ptr = object_bytes.get();

    int inject_hash_ret;
    testing::internal::CaptureStderr();

    inject_hash_ret = inject_hash_no_write(bad_hash_lib_filename.c_str(), 1,
                             &object_bytes_ptr, &object_bytes_size);
    std::string captured_stderr = testing::internal::GetCapturedStderr();

    ASSERT_EQ(0, inject_hash_ret);
    EXPECT_TRUE(captured_stderr.find("Error finding hash") != std::string::npos);
}

TEST_F(InjectHashTestFixture, TestBadMarkerLib) {
    std::unique_ptr<uint8_t> object_bytes(nullptr);
    size_t object_bytes_size;

    uint8_t *object_bytes_ptr = object_bytes.get();

    int inject_hash_ret;
    testing::internal::CaptureStderr();

    inject_hash_ret = inject_hash_no_write(bad_marker_lib_filename.c_str(), 1,
                             &object_bytes_ptr, &object_bytes_size);
    std::string captured_stderr = testing::internal::GetCapturedStderr();

    ASSERT_EQ(0, inject_hash_ret);
    EXPECT_TRUE(captured_stderr.find("Could not find .text module start symbol in object") != std::string::npos);
}
