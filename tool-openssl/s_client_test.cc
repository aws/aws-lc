// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
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
