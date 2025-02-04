// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#if defined(BORINGSSL_FIPS)
#include <gtest/gtest.h>
#include <openssl/crypto.h>
#include <openssl/ec_key.h>
#include <openssl/nid.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>

#include "internal.h"

extern "C" {
  OPENSSL_EXPORT void AWS_LC_fips_failure_callback(const char* message);
}

void AWS_LC_fips_failure_callback(const char* message) {
  ASSERT_EQ(1, FIPS_mode());

  // TODO update the self test to report the actual test that failed
  const std::map<std::string, std::string> kat_failure_messages = {
    {"HMAC-SHA-256", "Integrity test failed"},
    {"AES-CBC-encrypt", "Self-tests failed"},
    {"AES-CBC-decrypt", "Self-tests failed"},
    {"AES-GCM-encrypt", "Self-tests failed"},
    {"AES-GCM-decrypt", "Self-tests failed"},
    {"DRBG", "Self-tests failed"},
    {"DRBG-reseed", "Self-tests failed"},
    {"SHA-1", "Self-tests failed"},
    {"SHA-256", "Integrity test failed"},
    {"SHA-512", "Self-tests failed"},
    {"TLS-KDF", "Self-tests failed"},
    {"RSA-sign", "RSA self-tests failed"},
    {"RSA-verify", "RSA self-tests failed"},
    {"ECDSA-sign", "ECC self-tests failed"},
    {"ECDSA-verify", "ECC self-tests failed"},
    {"Z-computation", "ECC self-tests failed"},
    {"FFDH", "FFDH self-tests failed"},
    {"RSA_PWCT", "RSA PCT failed"},
    {"ECDSA_PWCT", "EC PCT failed"}
  };

  char* broken_kat = getenv("FIPS_CALLBACK_TEST_EXPECTED_FAILURE");
  if (broken_kat != nullptr) {
    auto expected_message = kat_failure_messages.find(broken_kat);
    if (expected_message != kat_failure_messages.end()) {
      ASSERT_STREQ(expected_message->second.c_str(), message);
    } else {
      FAIL() << "Failed to find expected message for FIPS_CALLBACK_TEST_POWER_ON_TEST_FAILURE=" << broken_kat;
    }

  } else {
    FAIL() << "AWS_LC_fips_failure_callback called when no KAT was expected to be broken";
  }
  fprintf(stderr, "AWS-LC FIPS callback passed\n");
}

TEST(FIPSCallback, PowerOnSelfTests) {
  // Some KATs are lazy and run on first use
  boringssl_ensure_rsa_self_test();
  boringssl_ensure_ecc_self_test();
  boringssl_ensure_ffdh_self_test();
  boringssl_ensure_ml_kem_self_test();
  boringssl_ensure_eddsa_self_test();
  boringssl_ensure_hasheddsa_self_test();

  char* broken_kat = getenv("FIPS_CALLBACK_TEST_POWER_ON_TEST_FAILURE");
  if (broken_kat != nullptr) {
    // A kat was supposed to be broken and the self tests should have failed by now
    FAIL() << "FIPS_CALLBACK_TEST_POWER_ON_TEST_FAILURE=" << broken_kat
      << " and should have failed the self tests and aborted before this" <<
        "function can run";
  } else {
    // break-kat.go has not run and corrupted this test yet, everything should work
    ASSERT_TRUE(BORINGSSL_self_test());
  }
}

TEST(FIPSCallback, RSARuntimeTest) {
  // At this point the library has loaded, if a self test was broken
  // the process would have aborted already
  ASSERT_EQ(1, FIPS_mode());
  ASSERT_EQ(1, BORINGSSL_self_test());

  char*broken_runtime_test = getenv("BORINGSSL_FIPS_BREAK_TEST");
  bssl::UniquePtr<RSA> rsa(RSA_new());
  // This should either pass or abort
  EXPECT_TRUE(RSA_generate_key_fips(rsa.get(), 2048, nullptr));
  if (broken_runtime_test != nullptr && strcmp(broken_runtime_test, "RSA_PWCT" ) == 0) {
    FAIL() << "FIPS_CALLBACK_TEST_POWER_ON_TEST_FAILURE=RSA_PWCT and should have"
          " failed the self tests and aborted before here";
  }
}

TEST(FIPSCallback, ECDSARuntimeTest) {
  // At this point the library has loaded, if a self test was broken
  // the process would have aborted already
  ASSERT_EQ(1, FIPS_mode());
  ASSERT_EQ(1, BORINGSSL_self_test());

  char*broken_runtime_test = getenv("BORINGSSL_FIPS_BREAK_TEST");
  // This should either pass or abort
  bssl::UniquePtr<EC_KEY> key(EC_KEY_new_by_curve_name(NID_X9_62_prime256v1));
  EXPECT_TRUE(EC_KEY_generate_key_fips(key.get()));
  if (broken_runtime_test != nullptr && (strcmp(broken_runtime_test, "ECDSA_PWCT" ) == 0 ||
                                         strcmp(broken_runtime_test, "CRNG" ) == 0)) {
    FAIL() << "FIPS_CALLBACK_TEST_POWER_ON_TEST_FAILURE=ECDSA_PWCT and should have"
          " failed the self tests and aborted before here";
  }
}

#endif
