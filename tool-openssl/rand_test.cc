// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>

#include <gtest/gtest.h>
#include <climits>
#include <string>
#include <vector>
#if !defined(OPENSSL_WINDOWS)
#include <signal.h>
#include <sys/resource.h>
#include <unistd.h>
#endif
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

class RandTempFileTest : public ::testing::Test {
 protected:
  void TearDown() override {
    for (const auto &path : temp_paths_) {
      RemoveFile(path);
    }
  }

  char *CreateTempPath() {
    temp_paths_.push_back(new char[PATH_MAX]);
    char *path = temp_paths_.back();
    EXPECT_GT(createTempFILEpath(path), 0u);
    return path;
  }

  ~RandTempFileTest() override {
    for (auto *p : temp_paths_) {
      delete[] p;
    }
  }

 private:
  std::vector<char *> temp_paths_;
};

TEST_F(RandTempFileTest, RawOutput) {
  char *out_path = CreateTempPath();
  args_list_t args = {"-out", out_path, "32"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string content = ReadFileToString(out_path);
  EXPECT_EQ(32u, content.size());
}

TEST_F(RandTempFileTest, Base64Output) {
  char *out_path = CreateTempPath();
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

TEST_F(RandTempFileTest, HexOutput) {
  char *out_path = CreateTempPath();
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
  args_list_t args = {"0"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST_F(RandTempFileTest, LastFormatWins) {
  char *out_path = CreateTempPath();

  args_list_t args1 = {"-base64", "-hex", "-out", out_path, "16"};
  EXPECT_EQ(kToolExitSuccess, randTool(args1));
  std::string content = ReadFileToString(out_path);
  EXPECT_EQ(33u, content.size());
  EXPECT_EQ('\n', content[32]);

  args_list_t args2 = {"-hex", "-base64", "-out", out_path, "16"};
  EXPECT_EQ(kToolExitSuccess, randTool(args2));
  content = ReadFileToString(out_path);
  EXPECT_GT(content.size(), 16u);
  for (char c : content) {
    EXPECT_TRUE(isalnum(c) || c == '+' || c == '/' || c == '=' || c == '\n');
  }
}

TEST_F(RandTempFileTest, LastOutWins) {
  char *path1 = CreateTempPath();
  char *path2 = CreateTempPath();
  args_list_t args = {"-out", path1, "-out", path2, "32"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string content1 = ReadFileToString(path1);
  std::string content2 = ReadFileToString(path2);
  EXPECT_TRUE(content1.empty());
  EXPECT_EQ(32u, content2.size());
}

TEST(RandTest, DashOutMeansStdout) {
  testing::internal::CaptureStdout();
  args_list_t args = {"-hex", "-out", "-", "16"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string captured = testing::internal::GetCapturedStdout();
  EXPECT_EQ(33u, captured.size());
}

TEST_F(RandTempFileTest, OutputIsRandom) {
  char *path1 = CreateTempPath();
  char *path2 = CreateTempPath();
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

TEST(RandTest, NumOverflow) {
  args_list_t args = {"99999999999999999999999"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST_F(RandTempFileTest, LargeRawOutput) {
  char *out_path = CreateTempPath();
  args_list_t args = {"-out", out_path, "100000"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string content = ReadFileToString(out_path);
  EXPECT_EQ(100000u, content.size());
}

TEST_F(RandTempFileTest, LargeBase64Output) {
  char *out_path = CreateTempPath();
  args_list_t args = {"-base64", "-out", out_path, "100000"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string content = ReadFileToString(out_path);
  EXPECT_FALSE(content.empty());
  for (char c : content) {
    EXPECT_TRUE(isalnum(c) || c == '+' || c == '/' || c == '=' || c == '\n')
        << "unexpected character: " << static_cast<int>(c);
  }
}

TEST_F(RandTempFileTest, LargeHexOutput) {
  char *out_path = CreateTempPath();
  args_list_t args = {"-hex", "-out", out_path, "100000"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string content = ReadFileToString(out_path);
  EXPECT_EQ(200001u, content.size());
  EXPECT_EQ('\n', content[200000]);
}

TEST_F(RandTempFileTest, OctalNum) {
  char *out_path = CreateTempPath();
  args_list_t args = {"-out", out_path, "010"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string content = ReadFileToString(out_path);
  EXPECT_EQ(8u, content.size());
}

TEST_F(RandTempFileTest, HexNum) {
  char *out_path = CreateTempPath();
  args_list_t args = {"-out", out_path, "0x10"};
  EXPECT_EQ(kToolExitSuccess, randTool(args));
  std::string content = ReadFileToString(out_path);
  EXPECT_EQ(16u, content.size());
}

TEST(RandTest, WhitespacePrefixedNegative) {
  args_list_t args = {" -1"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST(RandTest, NegativeCountWrap) {
  args_list_t args = {" -18446744073709551615"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST(RandTest, NewlinePrefixedNegative) {
  args_list_t args = {"\n-18446744073709551615"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST(RandTest, CarriageReturnPrefixedNegative) {
  args_list_t args = {"\r-1"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST(RandTest, VerticalTabPrefixedNegative) {
  args_list_t args = {"\v-1"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

TEST(RandTest, FormFeedPrefixedNegative) {
  args_list_t args = {"\f-1"};
  EXPECT_EQ(kToolExitFailure, randTool(args));
}

#if !defined(OPENSSL_WINDOWS)
static void WriteFailureTest(const char *out_path, const char *format_flag) {
  struct rlimit limit = {0, 0};
  if (setrlimit(RLIMIT_FSIZE, &limit) != 0 ||
      signal(SIGXFSZ, SIG_IGN) == SIG_ERR) {
    _exit(2);
  }
  args_list_t args;
  if (format_flag != nullptr) {
    args.push_back(format_flag);
  }
  args.push_back("-out");
  args.push_back(out_path);
  args.push_back("32");
  _exit(randTool(args));
}

TEST_F(RandTempFileTest, WriteFailureRaw) {
  char *out_path = CreateTempPath();
  ASSERT_EXIT(WriteFailureTest(out_path, nullptr),
              testing::ExitedWithCode(kToolExitFailure), "");
}

TEST_F(RandTempFileTest, WriteFailureBase64) {
  char *out_path = CreateTempPath();
  ASSERT_EXIT(WriteFailureTest(out_path, "-base64"),
              testing::ExitedWithCode(kToolExitFailure), "");
}

TEST_F(RandTempFileTest, WriteFailureHex) {
  char *out_path = CreateTempPath();
  ASSERT_EXIT(WriteFailureTest(out_path, "-hex"),
              testing::ExitedWithCode(kToolExitFailure), "");
}

static void BrokenPipeTest(const char *format_flag) {
  int pipefd[2];
  if (pipe(pipefd) != 0) {
    _exit(2);
  }
  close(pipefd[0]);
  if (dup2(pipefd[1], STDOUT_FILENO) == -1) {
    _exit(2);
  }
  close(pipefd[1]);
  signal(SIGPIPE, SIG_IGN);

  args_list_t args;
  if (format_flag != nullptr) {
    args.push_back(format_flag);
  }
  args.push_back("32");
  _exit(randTool(args));
}

TEST(RandTest, BrokenPipeRaw) {
  ASSERT_EXIT(BrokenPipeTest(nullptr),
              testing::ExitedWithCode(kToolExitFailure), "");
}

TEST(RandTest, BrokenPipeBase64) {
  ASSERT_EXIT(BrokenPipeTest("-base64"),
              testing::ExitedWithCode(kToolExitFailure), "");
}

TEST(RandTest, BrokenPipeHex) {
  ASSERT_EXIT(BrokenPipeTest("-hex"),
              testing::ExitedWithCode(kToolExitFailure), "");
}

static void UnbufferedBrokenPipeBase64Test() {
  int pipefd[2];
  if (pipe(pipefd) != 0) {
    _exit(2);
  }
  close(pipefd[0]);
  if (dup2(pipefd[1], STDOUT_FILENO) == -1) {
    _exit(2);
  }
  close(pipefd[1]);
  signal(SIGPIPE, SIG_IGN);
  setvbuf(stdout, NULL, _IONBF, 0);
  alarm(60);

  args_list_t args = {"-base64", "32"};
  _exit(randTool(args));
}

TEST(RandTest, UnbufferedBrokenPipeBase64) {
  ASSERT_EXIT(UnbufferedBrokenPipeBase64Test(),
              testing::ExitedWithCode(kToolExitFailure), "");
}
#endif
