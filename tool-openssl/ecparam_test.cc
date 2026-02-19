// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/bio.h>
#include <openssl/ec.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <algorithm>
#include <cctype>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"

namespace {

// -------------------- Helper Functions and Structures ------------------------

// Helper function to run commands and compare trimmed file outputs
void RunAndCompareCommands(const std::string &tool_cmd,
                           const std::string &openssl_cmd,
                           const std::string &tool_file,
                           const std::string &openssl_file) {
  ASSERT_EQ(system(tool_cmd.c_str()), 0)
      << "AWS-LC command failed: " << tool_cmd;
  ASSERT_EQ(system(openssl_cmd.c_str()), 0)
      << "OpenSSL command failed: " << openssl_cmd;

  std::string tool_content = ReadFileToString(tool_file);
  std::string openssl_content = ReadFileToString(openssl_file);
  ASSERT_EQ(trim(tool_content), trim(openssl_content));
}

// Test parameters for curve comparison tests
struct CurveTestParams {
  std::string curve_name;
  std::string test_name;

  CurveTestParams(const std::string &name, const std::string &test)
      : curve_name(name), test_name(test) {}
};

// Test parameters for key generation tests
struct KeyGenTestParams {
  const char *curve_name;
  const char *extra_args;
  const char *test_name;
  bool is_der;

  KeyGenTestParams(const char *name, const char *args, const char *test,
                   bool der)
      : curve_name(name), extra_args(args), test_name(test), is_der(der) {}
};

// Custom PrintTo functions to avoid Valgrind padding issues
void PrintTo(const CurveTestParams &params, std::ostream *os) {
  *os << "CurveTestParams{curve_name=\"" << params.curve_name
      << "\", test_name=\"" << params.test_name << "\"}";
}

void PrintTo(const KeyGenTestParams &params, std::ostream *os) {
  *os << "KeyGenTestParams{curve_name=\"" << params.curve_name
      << "\", extra_args=\"" << params.extra_args << "\", test_name=\""
      << params.test_name << "\", is_der=" << (params.is_der ? "true" : "false")
      << "}";
}

// Helper function to get all supported curves dynamically
std::vector<CurveTestParams> GetSupportedCurves() {
  std::vector<CurveTestParams> curves;

  size_t num_curves = EC_get_builtin_curves(nullptr, 0);
  std::vector<EC_builtin_curve> builtin_curves(num_curves);
  EC_get_builtin_curves(builtin_curves.data(), num_curves);

  for (const auto &curve : builtin_curves) {
    const char *sn = OBJ_nid2sn(curve.nid);
    if (sn) {
      std::string test_name = sn;
      std::transform(
          test_name.begin(), test_name.end(), test_name.begin(),
          [](char c) { return std::isalnum(c) ? std::toupper(c) : '_'; });
      curves.push_back({sn, test_name});
    }
  }

  return curves;
}

// -------------------- Basic Ecparam Functionality Tests ---------------------

class EcparamTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(key_path), 0u);
  }

  void TearDown() override {
    RemoveFile(out_path);
    RemoveFile(key_path);
  }

  char out_path[PATH_MAX] = {};
  char key_path[PATH_MAX] = {};
};

// Test basic functionality
TEST_F(EcparamTest, EcparamToolBasicTest) {
  args_list_t args = {"-name", "prime256v1", "-out", out_path};

  EXPECT_TRUE(ecparamTool(args)) << "Basic ecparam functionality failed";

  // Validate it's actually parseable EC parameters in PEM format
  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "r"));
  ASSERT_TRUE(bio) << "Cannot open output file";
  bssl::UniquePtr<EC_GROUP> group(
      PEM_read_bio_ECPKParameters(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(group) << "Output is not valid EC parameters";

  // Verify it's the correct curve
  ASSERT_EQ(NID_X9_62_prime256v1, EC_GROUP_get_curve_name(group.get()))
      << "Wrong curve in output";
}

// Test basic functionality
TEST_F(EcparamTest, secp256r1) {
  args_list_t args = {"-name", "secp256r1", "-out", out_path};

  EXPECT_TRUE(ecparamTool(args)) << "Basic ecparam functionality failed";

  // Validate it's actually parseable EC parameters in PEM format
  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "r"));
  ASSERT_TRUE(bio) << "Cannot open output file";
  bssl::UniquePtr<EC_GROUP> group(
      PEM_read_bio_ECPKParameters(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(group) << "Output is not valid EC parameters";

  // Verify it's the correct curve
  ASSERT_EQ(NID_X9_62_prime256v1, EC_GROUP_get_curve_name(group.get()))
      << "Wrong curve in output";
}

TEST_F(EcparamTest, EcparamToolNooutTest) {
  args_list_t args = {"-name", "prime256v1", "-noout", "-out", out_path};

  EXPECT_TRUE(ecparamTool(args)) << "Ecparam -noout failed";
  EXPECT_TRUE(ReadFileToString(out_path).empty())
      << "Output file should be empty with -noout";
}

TEST_F(EcparamTest, EcparamToolNooutExceptionTest) {
  args_list_t args = {"-name",  "prime256v1", "-genkey",
                      "-noout", "-out",       out_path};

  EXPECT_TRUE(ecparamTool(args)) << "Ecparam -genkey failed";

  // Validate it's actually a parseable EC key
  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "r"));
  ASSERT_TRUE(bio) << "Cannot open generated key file";
  bssl::UniquePtr<EVP_PKEY> pkey(
      PEM_read_bio_PrivateKey(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(pkey) << "Generated key is not parseable";
  ASSERT_EQ(EVP_PKEY_EC, EVP_PKEY_id(pkey.get()))
      << "Generated key is not EC type";

  // Verify it's the correct curve
  EC_KEY *ec_key = EVP_PKEY_get0_EC_KEY(pkey.get());
  ASSERT_TRUE(ec_key);
  const EC_GROUP *group = EC_KEY_get0_group(ec_key);
  ASSERT_EQ(NID_X9_62_prime256v1, EC_GROUP_get_curve_name(group))
      << "Wrong curve generated";
}

TEST_F(EcparamTest, EcparamToolGenkeyTest) {
  args_list_t args = {"-name", "prime256v1", "-genkey", "-out", out_path};

  EXPECT_TRUE(ecparamTool(args)) << "Ecparam -genkey failed";

  // Validate it's actually a parseable EC key
  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "r"));
  ASSERT_TRUE(bio) << "Cannot open generated key file";
  bssl::UniquePtr<EVP_PKEY> pkey(
      PEM_read_bio_PrivateKey(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(pkey) << "Generated key is not parseable";
  ASSERT_EQ(EVP_PKEY_EC, EVP_PKEY_id(pkey.get()))
      << "Generated key is not EC type";

  // Verify it's the correct curve
  EC_KEY *ec_key = EVP_PKEY_get0_EC_KEY(pkey.get());
  ASSERT_TRUE(ec_key);
  const EC_GROUP *group = EC_KEY_get0_group(ec_key);
  ASSERT_EQ(NID_X9_62_prime256v1, EC_GROUP_get_curve_name(group))
      << "Wrong curve generated";
}

TEST_F(EcparamTest, EcparamToolConvFormTest) {
  args_list_t args = {"-name",      "prime256v1", "-genkey", "-conv_form",
                      "compressed", "-out",       out_path};

  EXPECT_TRUE(ecparamTool(args)) << "Ecparam -conv_form failed";

  // Validate it's a parseable EC key with compressed point format
  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "r"));
  ASSERT_TRUE(bio) << "Cannot open generated key file";
  bssl::UniquePtr<EVP_PKEY> pkey(
      PEM_read_bio_PrivateKey(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(pkey) << "Generated compressed key is not parseable";
  ASSERT_EQ(EVP_PKEY_EC, EVP_PKEY_id(pkey.get()))
      << "Generated key is not EC type";

  // Verify point compression setting
  EC_KEY *ec_key = EVP_PKEY_get0_EC_KEY(pkey.get());
  ASSERT_TRUE(ec_key);
  ASSERT_EQ(POINT_CONVERSION_COMPRESSED, EC_KEY_get_conv_form(ec_key))
      << "Key not using compressed format";
}

TEST_F(EcparamTest, EcparamToolOutformTest) {
  args_list_t args = {"-name", "prime256v1", "-outform",
                      "DER",   "-out",       out_path};

  EXPECT_TRUE(ecparamTool(args)) << "Ecparam -outform failed";

  // Validate it's actually DER format by parsing it
  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(bio) << "Cannot open DER output file";
  bssl::UniquePtr<EC_GROUP> group(d2i_ECPKParameters_bio(bio.get(), nullptr));
  ASSERT_TRUE(group) << "Output is not valid DER format";

  // Verify it's the correct curve
  ASSERT_EQ(NID_X9_62_prime256v1, EC_GROUP_get_curve_name(group.get()))
      << "Wrong curve in DER output";
}

// Error handling tests
class EcparamOptionUsageErrorsTest : public ::testing::Test {
 protected:
  void TestOptionUsageErrors(const args_list_t &args) {
    EXPECT_FALSE(ecparamTool(args));
  }
};

TEST_F(EcparamOptionUsageErrorsTest, InvalidCurveTest) {
  args_list_t args = {"-name", "invalid_curve"};
  TestOptionUsageErrors(args);
}

TEST_F(EcparamOptionUsageErrorsTest, InvalidConvFormTest) {
  args_list_t args = {"-name", "prime256v1", "-conv_form", "invalid"};
  TestOptionUsageErrors(args);
}

TEST_F(EcparamOptionUsageErrorsTest, InvalidOutformTest) {
  args_list_t args = {"-name", "prime256v1", "-outform", "INVALID"};
  TestOptionUsageErrors(args);
}

// -------------------- OpenSSL Comparison Tests ------------------------------

// Parameterized tests for curve parameter comparison
class EcparamCurveComparisonTest
    : public ::testing::Test,
      public ::testing::WithParamInterface<CurveTestParams> {
 protected:
  void SetUp() override {
    memset(out_path_tool, '\0', PATH_MAX);
    memset(out_path_openssl, '\0', PATH_MAX);
    tool_executable_path = getenv("AWS_LC_TOOL_EXECUTABLE_PATH");
    openssl_executable_path = getenv("OPENSSL_EXECUTABLE_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP()
          << "Skipping test: AWS_LC_TOOL_EXECUTABLE_PATH and/or "
             "OPENSSL_EXECUTABLE_PATH environment variables are not set";
    }
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
  }

  void TearDown() override {
    if (strnlen(out_path_tool, PATH_MAX) >
        0) {  // Only remove if path was created
      RemoveFile(out_path_tool);
    }
    if (strnlen(out_path_openssl, PATH_MAX) >
        0) {  // Only remove if path was created
      RemoveFile(out_path_openssl);
    }
  }

  const char *tool_executable_path;
  const char *openssl_executable_path;
  char out_path_tool[PATH_MAX] = {};
  char out_path_openssl[PATH_MAX] = {};
};

TEST_P(EcparamCurveComparisonTest, CompareParameters) {
  const auto &params = GetParam();
  std::string tool_command = std::string(tool_executable_path) +
                             " ecparam -name " + params.curve_name + " > " +
                             out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " ecparam -name " + params.curve_name + " > " +
                                out_path_openssl;
  RunAndCompareCommands(tool_command, openssl_command, out_path_tool,
                        out_path_openssl);
}

INSTANTIATE_TEST_SUITE_P(
    CurveTests, EcparamCurveComparisonTest,
    ::testing::ValuesIn(GetSupportedCurves()),
    [](const ::testing::TestParamInfo<CurveTestParams> &info) {
      return info.param.test_name;
    });

// Parameterized tests for key generation compatibility
class EcparamKeyGenComparisonTest
    : public ::testing::Test,
      public ::testing::WithParamInterface<KeyGenTestParams> {
 protected:
  void SetUp() override {
    memset(key_path_tool, '\0', PATH_MAX);
    tool_executable_path = getenv("AWS_LC_TOOL_EXECUTABLE_PATH");
    openssl_executable_path = getenv("OPENSSL_EXECUTABLE_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP()
          << "Skipping test: AWS_LC_TOOL_EXECUTABLE_PATH and/or "
             "OPENSSL_EXECUTABLE_PATH environment variables are not set";
    }
    ASSERT_GT(createTempFILEpath(key_path_tool), 0u);
  }

  void TearDown() override {
    if (strnlen(key_path_tool, PATH_MAX) >
        0) {  // Only remove if path was created
      RemoveFile(key_path_tool);
    }
  }

  const char *tool_executable_path;
  const char *openssl_executable_path;
  char key_path_tool[PATH_MAX] = {};
};

TEST_P(EcparamKeyGenComparisonTest, KeyGenCompatibility) {
  const auto &params = GetParam();
  std::string tool_command = std::string(tool_executable_path) +
                             " ecparam -name " + params.curve_name +
                             " -genkey " + params.extra_args + " -out " +
                             key_path_tool;

  ASSERT_EQ(system(tool_command.c_str()), 0);

  // Test that OpenSSL CLI can read AWS-LC generated key
  std::string inform_flag = params.is_der ? " -inform DER" : "";
  std::string openssl_read = std::string(openssl_executable_path) +
                             " pkey -in " + key_path_tool + inform_flag +
                             " -noout";
  ASSERT_EQ(system(openssl_read.c_str()), 0)
      << "OpenSSL cannot read AWS-LC generated key: " << params.test_name;
}

INSTANTIATE_TEST_SUITE_P(
    KeyGenTests, EcparamKeyGenComparisonTest,
    ::testing::Values(
        KeyGenTestParams{"prime256v1", "", "Structure", false},
        KeyGenTestParams{"prime256v1", "-conv_form compressed", "Compressed",
                         false},
        KeyGenTestParams{"secp384r1", "-conv_form uncompressed", "Uncompressed",
                         false},
        KeyGenTestParams{"secp256k1", "-outform DER", "DER", true},
        KeyGenTestParams{"prime256v1", "-conv_form compressed -outform DER",
                         "CombinedOptions", true}),
    [](const ::testing::TestParamInfo<KeyGenTestParams> &info) {
      return info.param.test_name;
    });

// Additional specialized comparison tests
class EcparamComparisonTest : public ::testing::Test {
 protected:
  void SetUp() override {
    memset(out_path_tool, '\0', PATH_MAX);
    memset(out_path_openssl, '\0', PATH_MAX);
    memset(key_path_tool, '\0', PATH_MAX);
    memset(key_path_openssl, '\0', PATH_MAX);
    tool_executable_path = getenv("AWS_LC_TOOL_EXECUTABLE_PATH");
    openssl_executable_path = getenv("OPENSSL_EXECUTABLE_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP()
          << "Skipping test: AWS_LC_TOOL_EXECUTABLE_PATH and/or "
             "OPENSSL_EXECUTABLE_PATH environment variables are not set";
    }
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(key_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(key_path_openssl), 0u);
  }

  void TearDown() override {
    if (strnlen(out_path_tool, PATH_MAX) >
        0) {  // Only remove if path was created
      RemoveFile(out_path_tool);
    }
    if (strnlen(out_path_openssl, PATH_MAX) >
        0) {  // Only remove if path was created
      RemoveFile(out_path_openssl);
    }
    if (strnlen(key_path_tool, PATH_MAX) >
        0) {  // Only remove if path was created
      RemoveFile(key_path_tool);
    }
    if (strnlen(key_path_openssl, PATH_MAX) >
        0) {  // Only remove if path was created
      RemoveFile(key_path_openssl);
    }
  }

  const char *tool_executable_path;
  const char *openssl_executable_path;

  char out_path_tool[PATH_MAX] = {};
  char out_path_openssl[PATH_MAX] = {};
  char key_path_tool[PATH_MAX] = {};
  char key_path_openssl[PATH_MAX] = {};
};

// Test against OpenSSL output "openssl ecparam -name prime256v1 -noout"
TEST_F(EcparamComparisonTest, EcparamToolCompareNooutOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) +
                             " ecparam -name prime256v1 -noout > " +
                             out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " ecparam -name prime256v1 -noout > " +
                                out_path_openssl;

  ASSERT_EQ(system(tool_command.c_str()), 0);
  ASSERT_EQ(system(openssl_command.c_str()), 0);
  ASSERT_TRUE(ReadFileToString(out_path_tool).empty());
  ASSERT_TRUE(ReadFileToString(out_path_openssl).empty());
}

// Test against OpenSSL output "openssl ecparam -name prime256v1 -outform DER"
TEST_F(EcparamComparisonTest, EcparamToolCompareDERFormatOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) +
                             " ecparam -name prime256v1 -outform DER -out " +
                             out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " ecparam -name prime256v1 -outform DER -out " +
                                out_path_openssl;

  ASSERT_EQ(system(tool_command.c_str()), 0);
  ASSERT_EQ(system(openssl_command.c_str()), 0);
  ASSERT_EQ(ReadFileToString(out_path_tool),
            ReadFileToString(out_path_openssl));
}

// Test against OpenSSL output "openssl ecparam -name prime256v1 -out file"
TEST_F(EcparamComparisonTest, EcparamToolCompareFileOutputOpenSSL) {
  std::string tool_command = std::string(tool_executable_path) +
                             " ecparam -name prime256v1 -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " ecparam -name prime256v1 -out " +
                                out_path_openssl;
  RunAndCompareCommands(tool_command, openssl_command, out_path_tool,
                        out_path_openssl);
}

}  // namespace
