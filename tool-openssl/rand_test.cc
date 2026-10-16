// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <climits>
#include <string>
#include "internal.h"
#include "test_util.h"

TEST(RandTest, Help) {
  args_list_t args = {"-help"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
}

TEST(RandTest, MissingNum) {
  args_list_t args = {};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST(RandTest, InvalidNum) {
  args_list_t args = {"notanumber"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST(RandTest, NegativeNum) {
  args_list_t args = {"-1"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST(RandTest, TooManyArgs) {
  args_list_t args = {"16", "32"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST(RandTest, RawOutput) {
  char out_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(out_path), 0u);
  args_list_t args = {"-out", out_path, "32"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string content = ReadFileToString(out_path);
  EXPECT_EQ(32u, content.size());
}

TEST(RandTest, Base64Output) {
  char out_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(out_path), 0u);
  args_list_t args = {"-base64", "-out", out_path, "32"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string content = ReadFileToString(out_path);
  EXPECT_FALSE(content.empty());
  // Base64 of 32 bytes is 44 chars + newline
  EXPECT_GT(content.size(), 32u);
  // Verify only valid base64 characters (plus newline)
  for (char c : content) {
    EXPECT_TRUE(isalnum(c) || c == '+' || c == '/' || c == '=' || c == '\n')
        << "unexpected character: " << static_cast<int>(c);
  }
}

TEST(RandTest, HexOutput) {
  char out_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(out_path), 0u);
  args_list_t args = {"-hex", "-out", out_path, "16"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string content = ReadFileToString(out_path);
  // 16 bytes = 32 hex chars + newline
  EXPECT_EQ(33u, content.size());
  for (size_t i = 0; i < 32; i++) {
    EXPECT_TRUE(isxdigit(content[i]))
        << "non-hex character at position " << i;
  }
  EXPECT_EQ('\n', content[32]);
}

TEST(RandTest, ZeroBytes) {
  char out_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(out_path), 0u);
  args_list_t args = {"-out", out_path, "0"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string content = ReadFileToString(out_path);
  EXPECT_EQ(0u, content.size());
}

TEST(RandTest, Base64AndHexMutuallyExclusive) {
  args_list_t args = {"-base64", "-hex", "16"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST(RandTest, OutputIsRandom) {
  char path1[PATH_MAX], path2[PATH_MAX];
  ASSERT_GT(createTempFILEpath(path1), 0u);
  ASSERT_GT(createTempFILEpath(path2), 0u);
  args_list_t args1 = {"-out", path1, "32"};
  args_list_t args2 = {"-out", path2, "32"};
  EXPECT_EQ(kToolExitSuccess, randTool(args1));
  EXPECT_EQ(kToolExitSuccess, randTool(args2));
  std::string content1 = ReadFileToString(path1);
  std::string content2 = ReadFileToString(path2);
  EXPECT_EQ(32u, content1.size());
  EXPECT_EQ(32u, content2.size());
  EXPECT_NE(content1, content2);
}

TEST(RandTest, NumTooLarge) {
  args_list_t args = {"999999999999"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}
