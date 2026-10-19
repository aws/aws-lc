// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <climits>
#include <cstring>
#include <string>
#include "internal.h"
#include "test_util.h"

// Executable-level tests for cipher-name-as-command dispatch (tool.cc).
// These invoke the openssl binary and require AWSLC_TOOL_PATH.

class CipherAliasTest : public ::testing::Test {
 protected:
  void SetUp() override {
    tool_path = getenv("AWSLC_TOOL_PATH");
    if (tool_path == nullptr) {
      GTEST_SKIP() << "AWSLC_TOOL_PATH not set";
    }
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path1), 0u);
    ASSERT_GT(createTempFILEpath(out_path2), 0u);

    ScopedFILE f(fopen(in_path, "wb"));
    ASSERT_TRUE(f);
    const char *data = "Test data for cipher alias dispatch testing.";
    fwrite(data, 1, strlen(data), f.get());
  }

  void TearDown() override {
    if (tool_path != nullptr) {
      RemoveFile(in_path);
      RemoveFile(out_path1);
      RemoveFile(out_path2);
    }
  }

  const char *tool_path;
  char in_path[PATH_MAX];
  char out_path1[PATH_MAX];
  char out_path2[PATH_MAX];
};

TEST_F(CipherAliasTest, EncryptMatchesEnc) {
  std::string key(64, '1');
  std::string iv(32, '2');

  std::string alias_cmd = ShellEscape(tool_path) +
      " aes-256-cbc -e -K " + key + " -iv " + iv +
      " -in " + ShellEscape(in_path) + " -out " + ShellEscape(out_path1);
  std::string enc_cmd = ShellEscape(tool_path) +
      " enc -aes-256-cbc -e -K " + key + " -iv " + iv +
      " -in " + ShellEscape(in_path) + " -out " + ShellEscape(out_path2);

  ASSERT_EQ(0, ExecuteCommandExitCode(alias_cmd));
  ASSERT_EQ(0, ExecuteCommandExitCode(enc_cmd));

  std::string alias_out = ReadFileToString(out_path1);
  std::string enc_out = ReadFileToString(out_path2);
  EXPECT_FALSE(alias_out.empty());
  EXPECT_EQ(alias_out, enc_out);
}

TEST_F(CipherAliasTest, DecryptRoundTrip) {
  std::string key(64, '1');
  std::string iv(32, '2');

  std::string enc_cmd = ShellEscape(tool_path) +
      " enc -aes-256-cbc -e -K " + key + " -iv " + iv +
      " -in " + ShellEscape(in_path) + " -out " + ShellEscape(out_path1);
  ASSERT_EQ(0, ExecuteCommandExitCode(enc_cmd));

  std::string alias_cmd = ShellEscape(tool_path) +
      " aes-256-cbc -d -K " + key + " -iv " + iv +
      " -in " + ShellEscape(out_path1) + " -out " + ShellEscape(out_path2);
  ASSERT_EQ(0, ExecuteCommandExitCode(alias_cmd));

  std::string original = ReadFileToString(in_path);
  std::string decrypted = ReadFileToString(out_path2);
  EXPECT_EQ(original, decrypted);
}

TEST_F(CipherAliasTest, NoCommandFails) {
  std::string cmd = ShellEscape(tool_path);
  EXPECT_NE(0, ExecuteCommandExitCode(cmd));
}

TEST_F(CipherAliasTest, UnknownCommandFails) {
  std::string cmd = ShellEscape(tool_path) + " notacommand";
  EXPECT_NE(0, ExecuteCommandExitCode(cmd));
}

TEST_F(CipherAliasTest, UnsupportedCipherFails) {
  std::string key(64, '1');
  std::string iv(24, '2');
  std::string cmd = ShellEscape(tool_path) +
      " aes-256-gcm -e -K " + key + " -iv " + iv +
      " -in " + ShellEscape(in_path) + " -out " + ShellEscape(out_path1);
  EXPECT_NE(0, ExecuteCommandExitCode(cmd));
}
