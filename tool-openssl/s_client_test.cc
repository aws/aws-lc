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
  ASSERT_TRUE(result);
}

// Test -connect, -verify, -showcerts
TEST(SClientTest, SClientConnectVerifyShowcerts) {
  args_list_t args = {"-connect", "amazon.com:443", "-verify", "99"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

// Test -cipher
TEST(SClientTest, SClientCipher) {
  args_list_t args = {"-connect", "amazon.com:443", "-cipher", "AES128-SHA"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

// Test -tls1_1
TEST(SClientTest, SClientTls1_1) {
  args_list_t args = {"-connect", "amazon.com:443", "-tls1_1"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

// Test -cipher and -tls1_1 together
TEST(SClientTest, SClientCipherAndTls1_1) {
  args_list_t args = {"-connect", "amazon.com:443", "-cipher", "AES128-SHA", "-tls1_1"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

