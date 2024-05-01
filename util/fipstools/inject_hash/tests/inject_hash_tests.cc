// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <assert.h>
#include <iostream>
#include <string>

#include "inject_hash_tests.h"

constexpr char const *InjectHashTestFixture::good_lib_filename;
constexpr char const *InjectHashTestFixture::bad_hash_lib_filename;

TEST_F(InjectHashTestFixture, TestGoodLib) {
    uint8_t *object_bytes = nullptr;
    size_t object_bytes_size;

    ASSERT_EQ(1, inject_hash_no_write(NULL, const_cast<char*>(good_lib_filename), const_cast<char*>(good_lib_filename), 1, &object_bytes, &object_bytes_size));
}

TEST_F(InjectHashTestFixture, TestBadHashLib) {
    uint8_t *object_bytes = nullptr;
    size_t object_bytes_size;

    int inject_hash_ret;
    testing::internal::CaptureStderr();

    inject_hash_ret = inject_hash_no_write(NULL, const_cast<char*>(bad_hash_lib_filename), const_cast<char*>(bad_hash_lib_filename), 1, &object_bytes, &object_bytes_size);
    std::string captured_stderr = testing::internal::GetCapturedStderr();

    ASSERT_EQ(0, inject_hash_ret);
    EXPECT_TRUE(captured_stderr.find("Error finding hash") != std::string::npos);
}
