// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include "internal.h"

// Tests that connect to a live, remote host are in
// s_client_integration_test.cc, built into the integration_test executable.

// Test without connect but with help
TEST(SClientTest, NoConnect) {
  args_list_t args = {};
  int result = SClientTool(args);
  ASSERT_EQ(kToolExitFailure, result);
}

// Test -help
TEST(SClientTest, Help) {
  args_list_t args = {"-help"};
  int result = SClientTool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test that s_client returns false (not crash) for unresolvable hostname. This
// only needs DNS resolution to fail, not network egress, so it stays here
// rather than moving to s_client_integration_test.cc.
TEST(SClientTest, UnresolvableHost) {
  args_list_t args = {"-connect", "this.host.does.not.exist.invalid:443"};
  int result = SClientTool(args);
  ASSERT_EQ(kToolExitFailure, result);
}

TEST(SClientTest, NoCipherMatch) {
  ERR_clear_error();
  args_list_t args = {"-connect", "this.host.does.not.exist.invalid:443",
                      "-cipher", "LOW:KEY"};
  EXPECT_EQ(kToolExitFailure, SClientTool(args));

  const uint32_t err = ERR_peek_last_error();
  EXPECT_EQ(ERR_LIB_SSL, ERR_GET_LIB(err));
  EXPECT_EQ(SSL_R_NO_CIPHER_MATCH, ERR_GET_REASON(err));
  ERR_clear_error();
}

TEST(SClientTest, UnknownCipherIsIgnored) {
  ERR_clear_error();
  args_list_t args = {"-connect", "this.host.does.not.exist.invalid:443",
                      "-cipher", "ECDHE-RSA-AES128-GCM-SHA256:BOGUS"};
  EXPECT_EQ(kToolExitFailure, SClientTool(args));

  for (uint32_t err; (err = ERR_get_error()) != 0;) {
    if (ERR_GET_LIB(err) == ERR_LIB_SSL) {
      EXPECT_NE(SSL_R_NO_CIPHER_MATCH, ERR_GET_REASON(err));
      EXPECT_NE(SSL_R_INVALID_COMMAND, ERR_GET_REASON(err));
    }
  }
}
