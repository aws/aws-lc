// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <assert.h>
#include <string>

#include "inject_hash_tests.h"

constexpr char const *InjectHashTestFixture::good_lib_filename;

// TODO: write tests here
TEST_F(InjectHashTestFixture, TestGoodLib) {
    int argc = 6;
    // string argv[] = {"./inject_hash", "-p", good_lib_filename, "-o", good_lib_filename, "-f"};
    // char *argv[] = {"./inject_hash", "-p", good_lib_filename, "-o", good_lib_filename, "-f"};
    char prog[] = "./inject_hash";
    char flag1[] = "-p";
    char flag2[] = "-o";
    char flag3[] = "-f";
    char *argv[] = {prog, flag1, const_cast<char*>(good_lib_filename), flag2, const_cast<char*>(good_lib_filename), flag3};

    ASSERT_EQ(1, inject_hash(argc, argv));
};
