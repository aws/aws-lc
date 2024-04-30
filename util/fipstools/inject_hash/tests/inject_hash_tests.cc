// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <assert.h>
#include <string>

#include "inject_hash_tests.h"

constexpr char const *InjectHashTestFixture::good_lib_filename;
constexpr char const *InjectHashTestFixture::bad_hash_lib_filename;

TEST_F(InjectHashTestFixture, TestGoodLib) {
    int argc = 6;
    char prog[] = "./inject_hash";
    char flag1[] = "-p";
    char flag2[] = "-o";
    char flag3[] = "-f";
    char *argv[] = {prog, flag1, const_cast<char*>(good_lib_filename), flag2, const_cast<char*>(good_lib_filename), flag3};

    // TODO: make sure that when we succeed, we don't actually write the correct hash to the file so repeat tests will pass
    ASSERT_EQ(1, inject_hash(argc, argv));
}

TEST_F(InjectHashTestFixture, TestBadHashLib) {
    int argc = 6;
    char prog[] = "./inject_hash";
    char flag1[] = "-p";
    char flag2[] = "-o";
    char flag3[] = "-f";
    char *argv[] = {prog, flag1, const_cast<char*>(bad_hash_lib_filename), flag2, const_cast<char*>(bad_hash_lib_filename), flag3};

    printf("%s\n", bad_hash_lib_filename);

    // TODO: make sure it fails for the right reason somehow
    ASSERT_EQ(0, inject_hash(argc, argv));
}
