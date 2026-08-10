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
  args_list_t args = {"-connect", "amazon.com:443", "-verify", "99", "-showcerts"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}

// Test -cipher
TEST(SClientTest, Cipher) {
  // Pin to TLS 1.2 so the -cipher list is actually enforced. Without a version
  // pin the handshake can negotiate TLS 1.3, whose cipher suites are configured
  // separately, leaving -cipher effectively ignored.
  args_list_t args = {"-connect", "amazon.com:443", "-cipher",
                      "ECDHE-RSA-AES128-GCM-SHA256", "-tls1_2"};
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
  // TLS 1.1 has no AEAD/SHA-256 suites, so this stays on a CBC-SHA1 cipher, but
  // prefer the forward-secret ECDHE variant over static-RSA AES128-SHA.
  args_list_t args = {"-connect", "amazon.com:443", "-cipher",
                      "ECDHE-RSA-AES128-SHA", "-tls1_1"};
  bool result = SClientTool(args);
  ASSERT_TRUE(result);
}
