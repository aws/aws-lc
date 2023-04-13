// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Weak symbols are only supported well on Linux platforms. The FIPS failure
// callback functions that attempt to use weak symbols in bcm.c are disabled
// on other platforms. Therefore, only run these tests on supported platforms.
#if defined(__ELF__) && defined(__GNUC__)

#include <gtest/gtest.h>
#include <openssl/nid.h>
#include <openssl/rand.h>
#include <algorithm>
#include <list>
#include <string>
#include "test/gtest_main.h"
using namespace std;

extern "C" {
OPENSSL_EXPORT void AWS_LC_fips_failure_callback(const char* error);
}

int failure_count = 0;
list<string> failure_messages = {};
void AWS_LC_fips_failure_callback(const char* error) {
  failure_count++;
  failure_messages.emplace_back(error);
}

static bool message_in_errors(const string& expected_message) {
  for (const auto& msg : failure_messages) {
    if (msg.find(expected_message) != string::npos) {
      return true;
    }
  }
  return false;
}

struct test_config {
  string expected_failure_message;
  int initial_failure_count;
  int expected_failure_count;
};

// If hmac sha-256 is broken the integrity check can not be trusted to check
// itself and fails earlier
const test_config integrity_test_config = {
    "BORINGSSL_integrity_test",
    1,
    2
};
vector<string> integrity_tests = {"SHA-256", "HMAC-SHA-256"};

// The fast tests run automatically at startup and will report a failure to
// the test callback immediately, and then again when BORINGSSL_self_test is called
const test_config fast_test_config = {
    "boringssl_self_test_startup",
    1,
    2
};

// The lazy tests are not run at power up, only when called directly with
// BORINGSSL_self_test, therefore the callback should have been called once
const test_config lazy_test_config = {
    "BORINGSSL_self_test",
    0,
    1
};

vector<string> lazy_tests = {"ECDSA-sign", "ECDSA-verify", "ECDH", "FFDH",
                             "RSA-sign", "RSA-verify", "Z-computation"};

TEST(FIPSCallback, PowerOnTests) {
  // At this point the library has loaded, if a self test was broken
  // AWS_LC_FIPS_Callback would have already been called. If this test
  // wasn't broken the call count should be zero
  char* broken_kat = getenv("FIPS_CALLBACK_TEST_POWER_ON_TEST_FAILURE");
  if (broken_kat != nullptr) {
    struct test_config config;
    if(find(integrity_tests.begin(), integrity_tests.end(), broken_kat) != integrity_tests.end()) {
      config = integrity_test_config;
    } else if (find(lazy_tests.begin(), lazy_tests.end(), broken_kat) != lazy_tests.end()) {
      config = lazy_test_config;
    } else {
      config = fast_test_config;
    }
    ASSERT_EQ(config.initial_failure_count, failure_count);

    // Trigger lazy tests to run
    ASSERT_EQ(0, BORINGSSL_self_test());
    ASSERT_EQ(config.expected_failure_count, failure_count);
    ASSERT_TRUE(message_in_errors(config.expected_failure_message));
  } else {
    // break-kat.go has not run and corrupted this test yet, everything should work
    ASSERT_EQ(1, BORINGSSL_self_test());
    ASSERT_EQ(0, failure_count);
    ASSERT_EQ(1, FIPS_mode());
  }
}

TEST(FIPSCallback, DRBGRuntime) {
  // At this point the library has loaded, if a self test was broken
  // AWS_LC_FIPS_Callback would have already been called. If this test
  // wasn't broken the call count should be zero
  char*broken_runtime_test = getenv("BORINGSSL_FIPS_BREAK_TEST");
  ASSERT_EQ(0, failure_count);
  ASSERT_EQ(1, FIPS_mode());
  uint8_t buf[10];
  if (broken_runtime_test != nullptr && strcmp(broken_runtime_test, "CRNG" ) == 0) {
    ASSERT_FALSE(RAND_bytes(buf, sizeof(buf)));
    // TODO: make AWS_LC_FIPS_error update a new global state so FIPS_mode returns 0
    ASSERT_EQ(1, FIPS_mode());
    ASSERT_EQ(1, failure_count);
  } else {
    // BORINGSSL_FIPS_BREAK_TEST has not been set and everything should work
    ASSERT_TRUE(RAND_bytes(buf, sizeof(buf)));
    ASSERT_EQ(1, FIPS_mode());
    ASSERT_EQ(0, failure_count);
  }
}

#endif
