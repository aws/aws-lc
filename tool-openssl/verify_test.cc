// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "openssl/x509.h"
#include "test_util.h"


class VerifyTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(ca_path), 0u);
    ASSERT_GT(createTempFILEpath(chain_path), 0u);
    ASSERT_GT(createTempFILEpath(in_path), 0u);

    bssl::UniquePtr<X509> x509;
    CreateAndSignX509Certificate(x509, nullptr);
    ASSERT_TRUE(x509);

    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));

    ScopedFILE ca_file(fopen(ca_path, "wb"));
    ASSERT_TRUE(ca_file);
    ASSERT_TRUE(PEM_write_X509(ca_file.get(), x509.get()));

    ScopedFILE chain_file(fopen(chain_path, "wb"));
    ASSERT_TRUE(chain_file);
    ASSERT_TRUE(PEM_write_X509(chain_file.get(), x509.get()));
  }
  void TearDown() override {
    RemoveFile(ca_path);
    RemoveFile(chain_path);
    RemoveFile(in_path);
  }
  char ca_path[PATH_MAX];
  char chain_path[PATH_MAX];
  char in_path[PATH_MAX];
};


// ----------------------------- Verify Option Tests
// -----------------------------

// Test -CAfile with self-signed certificate
TEST_F(VerifyTest, SelfSignedCertWithCAfileTest) {
  args_list_t args = {"-CAfile", ca_path, in_path};
  int result = VerifyTool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test certificate without -CAfile
TEST_F(VerifyTest, SelfSignedCertWithoutCAfile) {
  args_list_t args = {in_path};
  int result = VerifyTool(args);
  ASSERT_EQ(kToolExitFailure, result);
}

// Test certificate with -untrusted
TEST_F(VerifyTest, SelfSignedCertWithUntrustedChain) {
  args_list_t args = {"-untrusted", chain_path, in_path};
  int result = VerifyTool(args);
  ASSERT_EQ(kToolExitFailure, result);
}

// Test certificate with -untrusted and -CAfile
TEST_F(VerifyTest, SelfSignedCertWithCAFileAndUntrustedChain) {
  args_list_t args = {"-CAfile", ca_path, "-untrusted", chain_path, in_path};
  int result = VerifyTool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// ----------------------------- Verify Exit Codes
// ------------------------------
//
// OpenSSL's verify distinguishes option/setup errors (exit 1) from
// certificates that fail to load or verify (exit 2).

// A certificate that does not chain to the trust store exits with 2.
TEST_F(VerifyTest, VerificationFailureExitCode) {
  bssl::UniquePtr<X509> other;
  CreateAndSignX509Certificate(other, nullptr);
  ASSERT_TRUE(other);
  ScopedFILE ca_file(fopen(ca_path, "wb"));
  ASSERT_TRUE(ca_file);
  ASSERT_TRUE(PEM_write_X509(ca_file.get(), other.get()));
  ca_file.reset();

  args_list_t args = {"-CAfile", ca_path, in_path};
  ASSERT_EQ(2, VerifyTool(args));
}

// One failing input among several exits with 2.
TEST_F(VerifyTest, AnyFailingInputExitCode) {
  char missing_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(missing_path), 0u);
  RemoveFile(missing_path);

  args_list_t args = {"-CAfile", ca_path, in_path, missing_path};
  ASSERT_EQ(2, VerifyTool(args));
}

// An input certificate that cannot be parsed exits with 2.
TEST_F(VerifyTest, UnparseableInputExitCode) {
  ScopedFILE in_file(fopen(in_path, "wb"));
  ASSERT_TRUE(in_file);
  ASSERT_GT(fputs("not a certificate\n", in_file.get()), 0);
  in_file.reset();

  args_list_t args = {"-CAfile", ca_path, in_path};
  ASSERT_EQ(2, VerifyTool(args));
}

// Trust store and -untrusted setup problems exit with 1.
TEST_F(VerifyTest, SetupFailureExitCode) {
  char missing_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(missing_path), 0u);
  RemoveFile(missing_path);

  args_list_t missing_cafile = {"-CAfile", missing_path, in_path};
  EXPECT_EQ(kToolExitFailure, VerifyTool(missing_cafile));

  args_list_t missing_untrusted = {"-CAfile", ca_path, "-untrusted",
                                   missing_path, in_path};
  EXPECT_EQ(kToolExitFailure, VerifyTool(missing_untrusted));

  args_list_t unknown_option = {"-CAfile", ca_path, "-bogus", in_path};
  EXPECT_EQ(kToolExitFailure, VerifyTool(unknown_option));
}

// -------------------- Verify OpenSSL Comparison Tests
// --------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class VerifyComparisonTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Skip gtests if env variables not set
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                      "environment variables are not set";
    }

    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(ca_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);

    CreateAndSignX509Certificate(x509, nullptr);
    ASSERT_TRUE(x509);

    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));

    ScopedFILE ca_file(fopen(ca_path, "wb"));
    ASSERT_TRUE(ca_file);
    ASSERT_TRUE(PEM_write_X509(ca_file.get(), x509.get()));
  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(in_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
      RemoveFile(ca_path);
    }
  }

  char in_path[PATH_MAX];
  char ca_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  bssl::UniquePtr<X509> x509;
  const char *tool_executable_path;
  const char *openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

// Test against OpenSSL with -CAfile & self-signed cert fed in as a file
// "openssl verify -CAfile cert.pem cert.pem"
TEST_F(VerifyComparisonTest, CAFileSelfSigned) {
  std::string tool_command = std::string(tool_executable_path) +
                             " verify -CAfile " + ca_path + " " + in_path +
                             " &> " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " verify -CAfile " + ca_path + " " + in_path +
                                " &> " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL with -CAfile & 2 self-signed cert fed in as files
// "openssl verify -CAfile cert.pem cert.pem cert.pem"
TEST_F(VerifyComparisonTest, CAFileMultipleFiles) {
  std::string tool_command = std::string(tool_executable_path) +
                             " verify -CAfile " + ca_path + " " + in_path +
                             " " + in_path + " &> " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " verify -CAfile " + ca_path + " " + in_path +
                                " " + in_path + " &> " + out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test against OpenSSL with -CAfile & self-signed cert fed through stdin
// "cat cert.pem | openssl verify -CAfile cert.pem"
TEST_F(VerifyComparisonTest, CAFileSelfSignedStdin) {
  std::string tool_command = "cat " + std::string(ca_path) + " | " +
                             std::string(tool_executable_path) +
                             " verify -CAfile " + ca_path + " &> " +
                             out_path_tool;
  std::string openssl_command = "cat " + std::string(ca_path) + " | " +
                                std::string(openssl_executable_path) +
                                " verify -CAfile " + ca_path + " &> " +
                                out_path_openssl;

  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test that verify's exit status matches OpenSSL: 0 on success, 2 when a
// certificate fails to verify or load, and 1 for setup errors such as a
// missing -CAfile.
TEST_F(VerifyComparisonTest, ExitCodes) {
  char missing_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(missing_path), 0u);
  RemoveFile(missing_path);

  char other_ca_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(other_ca_path), 0u);
  bssl::UniquePtr<X509> other;
  CreateAndSignX509Certificate(other, nullptr);
  ASSERT_TRUE(other);
  {
    ScopedFILE other_ca_file(fopen(other_ca_path, "wb"));
    ASSERT_TRUE(other_ca_file);
    ASSERT_TRUE(PEM_write_X509(other_ca_file.get(), other.get()));
  }

  struct {
    std::string args;
    int expected_exit;
  } cases[] = {
      {std::string("-CAfile ") + ca_path + " " + in_path, 0},
      {std::string("-CAfile ") + other_ca_path + " " + in_path, 2},
      {std::string("-CAfile ") + ca_path + " " + in_path + " " + missing_path,
       2},
      {std::string("-CAfile ") + missing_path + " " + in_path, 1},
      {std::string("-CAfile ") + ca_path + " -untrusted " + missing_path + " " +
           in_path,
       1},
  };
  for (const auto &c : cases) {
    std::string tool_command = std::string(tool_executable_path) + " verify " +
                               c.args + " > " + out_path_tool + " 2>&1";
    std::string openssl_command = std::string(openssl_executable_path) +
                                  " verify " + c.args + " > " +
                                  out_path_openssl + " 2>&1";
    int tool_exit = ExecuteCommandExitCode(tool_command);
    int openssl_exit = ExecuteCommandExitCode(openssl_command);
    EXPECT_EQ(c.expected_exit, tool_exit) << "verify " << c.args;
    EXPECT_EQ(openssl_exit, tool_exit) << "verify " << c.args;
  }

  RemoveFile(other_ca_path);
}
