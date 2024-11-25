// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include "internal.h"
#include <openssl/ssl.h>

// Test -connect
TEST(SClientTest, SClientConnect) {
  args_list_t args = {"-connect", "amazon.com:443"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

// Test without connect but with help
TEST(SClientTest, SClientNoConnect) {
  args_list_t args = {};
  bool result = SClientTool(args);
  ASSERT_FALSE(result);
}

// Test -help
TEST(SClientTest, SClientHelp) {
  args_list_t args = {"-help"};
  bool result = SClientTool(args);
  ASSERT_FALSE(result);
}

// Test -connect, -verify, -showcerts
TEST(SClientTest, SClientConnectVerifyShowcerts) {
  args_list_t args = {"-connect", "amazon.com:443", "-verify", "99"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

