// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/base.h>
#include <openssl/bio.h>
#include <openssl/mem.h>
#include <openssl/pem.h>
#include <string>
#ifndef _WIN32
#include <fcntl.h>
#include <unistd.h>
#endif
#ifdef _WIN32
#include <stdlib.h>  // for _putenv_s
#include <windows.h> // for CreatePipe, SetStdHandle
#endif
#include "internal.h"
#include "test_util.h"

// Use PEM_BUFSIZE (defined in openssl/pem.h) for password buffer size testing
// to match the implementation in pass_util.cc

namespace {
// Helper functions to encapsulate common operations
void WriteTestFile(const char *path, const char *content,
                   bool preserve_newlines = false) {
  ScopedFILE file(fopen(path, "wb"));
  ASSERT_TRUE(file) << "Failed to open file: " << path;
  if (content && strlen(content) > 0) {
    if (preserve_newlines) {
      // Write content exactly as provided, including newlines
      ASSERT_GT(fprintf(file.get(), "%s", content), 0)
          << "Failed to write to file: " << path;
    } else {
      // Write content without trailing newline
      size_t bytes_written = fwrite(content, 1, strlen(content), file.get());
      ASSERT_GT(bytes_written, 0u)  // Compare with unsigned 0
          << "Failed to write to file: " << path;
    }
  }
  // If content is NULL or empty, we just create an empty file (no assertion
  // needed)
}

void SetTestEnvVar(const char *name, const char *value) {
#ifdef _WIN32
  _putenv_s(name, value);
#else
  setenv(name, value, 1);
#endif
}

void UnsetTestEnvVar(const char *name) {
#ifdef _WIN32
  _putenv_s(name, "");
#else
  unsetenv(name);
#endif
}
}  // namespace

// Base test fixture for pass_util tests
class PassUtilTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Create temporary files for testing using utility from
    // crypto/test/test_util.h
    ASSERT_GT(createTempFILEpath(pass_path), 0u)
        << "Failed to create first temp file path";
    ASSERT_GT(createTempFILEpath(pass_path2), 0u)
        << "Failed to create second temp file path";

    // Write test passwords using helper function
    WriteTestFile(pass_path, "testpassword");
    WriteTestFile(pass_path2, "anotherpassword");

    // Set up environment variable using helper function
    SetTestEnvVar("TEST_PASSWORD_ENV", "envpassword");
  }

  void TearDown() override {
    // Use RemoveFile from tool-openssl/test_util.h
    RemoveFile(pass_path);
    RemoveFile(pass_path2);
    UnsetTestEnvVar("TEST_PASSWORD_ENV");
  }

  char pass_path[PATH_MAX] = {};
  char pass_path2[PATH_MAX] = {};
};


TEST_F(PassUtilTest, FileEdgeCases) {
  // Test file truncation - exactly at buffer size - 1 without newline
  {
    std::string truncated_pass(PEM_BUFSIZE - 1, 'A');
    WriteTestFile(pass_path, truncated_pass.c_str());
  }

  Password source(std::string("file:") + pass_path);
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on truncated file";

  // Test file exceeding maximum length
  {
    std::string long_pass(PEM_BUFSIZE + 10, 'B');
    WriteTestFile(pass_path, long_pass.c_str());
  }

  source = Password(std::string("file:") + pass_path);
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on too long file content";

  // Test empty file
  {
    WriteTestFile(pass_path, "");
  }

  source = Password(std::string("file:") + pass_path);
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on empty file";

  // Test file with only newlines - should succeed with empty password (like
  // OpenSSL)
  {
    WriteTestFile(pass_path, "\n\n\n", true);  // preserve_newlines = true
  }

  source = Password(std::string("file:") + pass_path);
  bool result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed on newline-only file";
  EXPECT_TRUE(source.empty())
      << "Password should be empty from newline-only file";

  // Test file at buffer size - 1 with newline (should not trigger truncation)
  {
    std::string non_truncated_pass(PEM_BUFSIZE - 2, 'C');
    std::string content = non_truncated_pass + "\n";
    WriteTestFile(pass_path, content.c_str(),
                  true);  // preserve_newlines = true
  }

  source = Password(std::string("file:") + pass_path);
  result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result)
      << "Should succeed when file is at max length but has newline";
  EXPECT_EQ(source.get().length(), static_cast<size_t>(PEM_BUFSIZE - 2))
      << "Password should not include newline and should be max length - 2";

  // Test Windows carriage return behavior (CRLF)
  {
    WriteTestFile(pass_path, "windowspassword\r\n", true);
  }
  
  source = Password(std::string("file:") + pass_path);
  result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed with Windows CRLF line ending";
  EXPECT_EQ(source.get(), "windowspassword") << "Should trim both \\r and \\n from Windows CRLF";

  // Test old Mac carriage return behavior (CR only)
  {
    WriteTestFile(pass_path, "macpassword\r", true);
  }
  
  source = Password(std::string("file:") + pass_path);
  result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed with old Mac CR line ending";
  EXPECT_EQ(source.get(), "macpassword") << "Should trim \\r from old Mac line ending";

  // Test mixed trailing line endings
  {
    WriteTestFile(pass_path, "mixedpassword\r\n\r", true);
  }
  
  source = Password(std::string("file:") + pass_path);
  result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed with mixed trailing line endings";
  EXPECT_EQ(source.get(), "mixedpassword") << "Should trim multiple trailing \\r and \\n characters";

  // Test password with embedded carriage return (should be preserved)
  {
    WriteTestFile(pass_path, "pass\rwith\rembedded\r\n", true);
  }
  
  source = Password(std::string("file:") + pass_path);
  result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed with embedded carriage returns";
  EXPECT_EQ(source.get(), "pass\rwith\rembedded") << "Embedded \\r should be preserved, only trailing trimmed";

  // Test file with only CRLF
  {
    WriteTestFile(pass_path, "\r\n", true);
  }
  
  source = Password(std::string("file:") + pass_path);
  result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed on CRLF-only file";
  EXPECT_TRUE(source.empty()) << "CRLF-only file should result in empty password";

  // Test file with multiple CRLF lines
  {
    WriteTestFile(pass_path, "\r\n\r\n\r\n", true);
  }
  
  source = Password(std::string("file:") + pass_path);
  result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed on multiple CRLF-only lines";
  EXPECT_TRUE(source.empty()) << "Multiple CRLF-only lines should result in empty password";
}


TEST_F(PassUtilTest, EnvVarEdgeCases) {
  // Test empty environment variable
  SetTestEnvVar("TEST_EMPTY_PASSWORD", "");

  Password source("env:TEST_EMPTY_PASSWORD");
  bool result = pass_util::ExtractPassword(source);
  EXPECT_FALSE(result) << "Should fail on empty environment variable";

  // Test maximum length environment variable
  std::string long_pass(PEM_BUFSIZE + 10, 'B');
  SetTestEnvVar("TEST_LONG_PASSWORD", long_pass.c_str());

  source = Password("env:TEST_LONG_PASSWORD");
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on too long environment variable";

  // Test non-existent environment variable
  source = Password("env:NON_EXISTENT_VAR_NAME_12345");
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on non-existent environment variable";

  UnsetTestEnvVar("TEST_EMPTY_PASSWORD");
  UnsetTestEnvVar("TEST_LONG_PASSWORD");
}

TEST_F(PassUtilTest, DirectPasswordEdgeCases) {
  // Test maximum length direct password
  std::string long_pass = "pass:" + std::string(PEM_BUFSIZE + 10, 'C');
  Password source(long_pass);
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on too long direct password";

  // Test empty direct password
  source = Password("pass:");
  bool result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed with empty direct password";
  EXPECT_TRUE(source.empty()) << "Password should be empty";

  // Test invalid format strings
  const char *invalid_formats[] = {
      "pass",           // Missing colon
      "pass:test:123",  // Multiple colons
      ":password",      // Missing prefix
      "invalid:pass",   // Invalid prefix
      "file:",          // Empty file path
      "env:",           // Empty environment variable
      "",               // Empty string
  };

  for (const char *fmt : invalid_formats) {
    source = Password(fmt);
    EXPECT_FALSE(pass_util::ExtractPassword(source))
        << "Should fail on invalid format: " << fmt;
  }
}

TEST_F(PassUtilTest, ExtractPasswordsDifferentFiles) {
  Password passin(std::string("file:") + pass_path);
  Password passout(std::string("file:") + pass_path2);

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(passin.get(), "testpassword");
  EXPECT_EQ(passout.get(), "anotherpassword");
}

TEST_F(PassUtilTest, ExtractPasswordsSameFile) {
  // Create file with two lines
  WriteTestFile(pass_path, "firstpassword\nsecondpassword\n", true);

  Password passin(std::string("file:") + pass_path);
  Password passout(std::string("file:") + pass_path);

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(passin.get(), "firstpassword");
  EXPECT_EQ(passout.get(), "secondpassword");

  // Test same-file functionality with Windows CRLF
  WriteTestFile(pass_path, "firstpass\r\nsecondpass\r\n", true);
  
  passin = Password(std::string("file:") + pass_path);
  passout = Password(std::string("file:") + pass_path);
  
  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(passin.get(), "firstpass") << "First line should have CRLF trimmed";
  EXPECT_EQ(passout.get(), "secondpass") << "Second line should have CRLF trimmed";

  // Test mixed line endings in same-file scenario
  WriteTestFile(pass_path, "unixpass\nsecondpass\r\n", true);
  
  passin = Password(std::string("file:") + pass_path);
  passout = Password(std::string("file:") + pass_path);
  
  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(passin.get(), "unixpass") << "Unix LF should be trimmed";
  EXPECT_EQ(passout.get(), "secondpass") << "Windows CRLF should be trimmed";
}

TEST_F(PassUtilTest, ExtractPasswordsMixedSources) {
  // Test file + environment variable
  Password passin(std::string("file:") + pass_path);
  Password passout("env:TEST_PASSWORD_ENV");

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(passin.get(), "testpassword");
  EXPECT_EQ(passout.get(), "envpassword");

  // Test direct password + file
  passin = Password("pass:directpass");
  passout = Password(std::string("file:") + pass_path2);

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(passin.get(), "directpass");
  EXPECT_EQ(passout.get(), "anotherpassword");
}

TEST_F(PassUtilTest, ExtractPasswordsEmptyPasswords) {
  // Both empty
  Password passin("");
  Password passout("");

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_TRUE(passin.empty());
  EXPECT_TRUE(passout.empty());

  // One empty, one with password
  passin = Password("");
  passout = Password("pass:onlypassout");

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_TRUE(passin.empty());
  EXPECT_EQ(passout.get(), "onlypassout");

  // Reverse: one with password, one empty
  passin = Password("pass:onlypassin");
  passout = Password("");

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(passin.get(), "onlypassin");
  EXPECT_TRUE(passout.empty());
}

TEST_F(PassUtilTest, ExtractPasswordsErrorCases) {
  // Invalid passin format
  Password passin("invalid:format");
  Password passout("pass:validpass");

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));

  // Invalid passout format
  passin = Password("pass:validpass");
  passout = Password("invalid:format");

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));

  // Both invalid formats
  passin = Password("invalid1:format");
  passout = Password("invalid2:format");

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));
}

TEST_F(PassUtilTest, ExtractPasswordsFileErrors) {
  // Non-existent file for passin
  Password passin("file:/non/existent/file1");
  Password passout("pass:validpass");

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));

  // Non-existent file for passout
  passin = Password("pass:validpass");
  passout = Password("file:/non/existent/file2");

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));

  // Same non-existent file for both
  passin = Password("file:/non/existent/samefile");
  passout = Password("file:/non/existent/samefile");

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));
}

TEST_F(PassUtilTest, ExtractPasswordsSameFileEdgeCases) {
  // File with only one line (passout should fail)
  WriteTestFile(pass_path, "onlyoneline", false);

  Password passin(std::string("file:") + pass_path);
  Password passout(std::string("file:") + pass_path);

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));

  // File with empty second line
  WriteTestFile(pass_path, "firstline\n\n", true);

  passin = Password(std::string("file:") + pass_path);
  passout = Password(std::string("file:") + pass_path);

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(passin.get(), "firstline");
  EXPECT_TRUE(passout.empty());

  // File with multiple lines (should only read first two)
  WriteTestFile(pass_path, "line1\nline2\nline3\nline4\n", true);

  passin = Password(std::string("file:") + pass_path);
  passout = Password(std::string("file:") + pass_path);

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(passin.get(), "line1");
  EXPECT_EQ(passout.get(), "line2");
}

#ifndef _WIN32
TEST_F(PassUtilTest, FdExtraction) {
  int fd = open(pass_path, O_RDONLY);
  ASSERT_GE(fd, 0);
  
  std::string fd_source = "fd:" + std::to_string(fd);
  Password source(fd_source);
  
  EXPECT_TRUE(pass_util::ExtractPassword(source));
  EXPECT_EQ(source.get(), "testpassword");
  
  close(fd);
  
  source = Password("fd:-1");
  EXPECT_FALSE(pass_util::ExtractPassword(source));
  
  source = Password("fd:invalid");
  EXPECT_FALSE(pass_util::ExtractPassword(source));
}
#endif

#ifndef _WIN32
TEST_F(PassUtilTest, StdinExtraction) {
  int pipefd[2];
  ASSERT_EQ(pipe(pipefd), 0);
  
  int old_stdin = dup(STDIN_FILENO);
  dup2(pipefd[0], STDIN_FILENO);
  
  ASSERT_EQ(write(pipefd[1], "stdinpass\n", 10), 10);
  close(pipefd[1]);
  
  Password source("stdin");
  EXPECT_TRUE(pass_util::ExtractPassword(source));
  EXPECT_EQ(source.get(), "stdinpass");
  
  dup2(old_stdin, STDIN_FILENO);
  close(old_stdin);
  close(pipefd[0]);
}
#else
TEST_F(PassUtilTest, StdinExtraction) {
  // Use existing temp file infrastructure instead of pipes
  WriteTestFile(pass_path, "stdinpass\n", true);
  
  // Redirect stdin to temp file using _dup2
  FILE* temp_file = fopen(pass_path, "r");
  ASSERT_TRUE(temp_file) << "Failed to open temp file";
  
  int old_stdin = _dup(_fileno(stdin));
  _dup2(_fileno(temp_file), _fileno(stdin));
  
  Password source("stdin");
  EXPECT_TRUE(pass_util::ExtractPassword(source));
  EXPECT_EQ(source.get(), "stdinpass");
  
  // Restore stdin
  _dup2(old_stdin, _fileno(stdin));
  _close(old_stdin);
  fclose(temp_file);
}
#endif

#ifndef _WIN32
TEST_F(PassUtilTest, StdinExtractPasswords) {
  int pipefd[2];
  ASSERT_EQ(pipe(pipefd), 0);
  
  int old_stdin = dup(STDIN_FILENO);
  dup2(pipefd[0], STDIN_FILENO);
  
  ASSERT_EQ(write(pipefd[1], "firstpass\nsecondpass\n", 20), 20);
  close(pipefd[1]);
  
  Password passin("stdin");
  Password passout("stdin");
  
  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(passin.get(), "firstpass");
  EXPECT_EQ(passout.get(), "secondpass");
  
  dup2(old_stdin, STDIN_FILENO);
  close(old_stdin);
  close(pipefd[0]);
}
#else
TEST_F(PassUtilTest, StdinExtractPasswords) {
  // Use existing temp file infrastructure for multi-line input
  WriteTestFile(pass_path, "firstpass\nsecondpass\n", true);
  
  // Redirect stdin to temp file using _dup2
  FILE* temp_file = fopen(pass_path, "r");
  ASSERT_TRUE(temp_file) << "Failed to open temp file";
  
  int old_stdin = _dup(_fileno(stdin));
  _dup2(_fileno(temp_file), _fileno(stdin));
  
  Password passin("stdin");
  Password passout("stdin");
  
  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(passin.get(), "firstpass");
  EXPECT_EQ(passout.get(), "secondpass");
  
  // Restore stdin
  _dup2(old_stdin, _fileno(stdin));
  _close(old_stdin);
  fclose(temp_file);
}
#endif
