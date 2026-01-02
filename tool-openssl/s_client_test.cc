// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/ssl.h>
#include "internal.h"

// Test -connect
TEST(SClientTest, Connect) {
  args_list_t args = {"-connect", "amazon.com:443"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

// Test without connect but with help
TEST(SClientTest, NoConnect) {
  args_list_t args = {};
  bool result = SClientTool(args);
  ASSERT_FALSE(result);
}

// Test -help
TEST(SClientTest, Help) {
  args_list_t args = {"-help"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

// Test -connect, -verify, -showcerts
TEST(SClientTest, ConnectVerifyShowcerts) {
  args_list_t args = {"-connect", "amazon.com:443", "-verify", "99"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

// Test -cipher
TEST(SClientTest, Cipher) {
  args_list_t args = {"-connect", "amazon.com:443", "-cipher", "AES128-SHA"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

// Test -tls1_1
TEST(SClientTest, Tls1_1) {
  args_list_t args = {"-connect", "amazon.com:443", "-tls1_1"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

// Test -cipher and -tls1_1 together
TEST(SClientTest, CipherAndTls1_1) {
  args_list_t args = {"-connect", "amazon.com:443", "-cipher", "AES128-SHA",
                      "-tls1_1"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}
