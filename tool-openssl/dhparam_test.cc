// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/dh.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"

namespace {

// -------------------- Helper Functions and Structures ------------------------


// Test parameters for bit size tests
struct BitSizeTestParams {
  unsigned numbits;
  std::string test_name;

  BitSizeTestParams(unsigned bits, const std::string &name)
      : numbits(bits), test_name(name) {}
};

// Custom PrintTo function to avoid Valgrind padding issues
void PrintTo(const BitSizeTestParams &params, std::ostream *os) {
  *os << "BitSizeTestParams{numbits=" << params.numbits << ", test_name=\""
      << params.test_name << "\"}";
}

// -------------------- Basic Dhparam Functionality Tests ---------------------

class DhparamTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(in_path), 0u);
  }

  void TearDown() override {
    RemoveFile(out_path);
    RemoveFile(in_path);
  }

  char out_path[PATH_MAX];
  char in_path[PATH_MAX];
};

// Test help option
TEST_F(DhparamTest, HelpOption) {
  args_list_t args = {"-help"};
  EXPECT_TRUE(dhparamTool(args));
}

// Test basic parameter generation
TEST_F(DhparamTest, BasicGeneration) {
  args_list_t args = {"-out", out_path, "512"};

  EXPECT_TRUE(dhparamTool(args)) << "Basic dhparam generation failed";

  // Validate it's actually parseable DH parameters in PEM format
  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "r"));
  ASSERT_TRUE(bio) << "Cannot open output file";
  bssl::UniquePtr<DH> dh(
      PEM_read_bio_DHparams(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(dh) << "Output is not valid DH parameters";

  // Verify bit size
  const BIGNUM *p = DH_get0_p(dh.get());
  ASSERT_TRUE(p);
  ASSERT_EQ(512u, static_cast<unsigned>(BN_num_bits(p)))
      << "Wrong bit size in output";

  // Verify generator is 2
  const BIGNUM *g = DH_get0_g(dh.get());
  ASSERT_TRUE(g);
  ASSERT_EQ(2u, BN_get_word(g)) << "Generator should be 2";
}

// Test generation with different bit sizes
TEST_F(DhparamTest, GenerateVariousSizes) {
  std::vector<unsigned> bit_sizes = {512, 1024};

  for (unsigned bits : bit_sizes) {
    args_list_t args = {"-out", out_path, std::to_string(bits)};
    EXPECT_TRUE(dhparamTool(args))
        << "Failed to generate " << bits << "-bit parameters";

    bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "r"));
    ASSERT_TRUE(bio);
    bssl::UniquePtr<DH> dh(
        PEM_read_bio_DHparams(bio.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(dh) << "Failed to parse " << bits << "-bit parameters";

    const BIGNUM *p = DH_get0_p(dh.get());
    ASSERT_TRUE(p);
    ASSERT_EQ(bits, static_cast<unsigned>(BN_num_bits(p))) << "Wrong bit size";
  }
}

// Test -noout flag
TEST_F(DhparamTest, NooutFlag) {
  args_list_t args = {"-noout", "-out", out_path, "512"};

  EXPECT_TRUE(dhparamTool(args)) << "dhparam -noout failed";
  EXPECT_TRUE(ReadFileToString(out_path).empty())
      << "Output file should be empty with -noout";
}

// Test -text flag
TEST_F(DhparamTest, TextOutput) {
  args_list_t args = {"-text", "-noout", "-out", out_path, "512"};

  EXPECT_TRUE(dhparamTool(args)) << "dhparam -text failed";

  std::string output = ReadFileToString(out_path);
  EXPECT_FALSE(output.empty()) << "Text output should not be empty";
  EXPECT_NE(output.find("DH Parameters:"), std::string::npos)
      << "Missing 'DH Parameters:' in output";
  EXPECT_NE(output.find("P:"), std::string::npos) << "Missing 'P:' in output";
  EXPECT_NE(output.find("G:"), std::string::npos) << "Missing 'G:' in output";
  EXPECT_NE(output.find("512 bit"), std::string::npos)
      << "Missing bit size in output";
}

// Test -text with encoded output
TEST_F(DhparamTest, TextWithEncodedOutput) {
  args_list_t args = {"-text", "-out", out_path, "512"};

  EXPECT_TRUE(dhparamTool(args)) << "dhparam -text with encoded output failed";

  std::string output = ReadFileToString(out_path);
  EXPECT_FALSE(output.empty());
  EXPECT_NE(output.find("DH Parameters:"), std::string::npos)
      << "Missing text output";
  EXPECT_NE(output.find("-----BEGIN DH PARAMETERS-----"), std::string::npos)
      << "Missing PEM output";
  EXPECT_NE(output.find("-----END DH PARAMETERS-----"), std::string::npos)
      << "Missing PEM end marker";
}

// Test DER output format
TEST_F(DhparamTest, DEROutputFormat) {
  args_list_t args = {"-outform", "DER", "-out", out_path, "512"};

  EXPECT_TRUE(dhparamTool(args)) << "dhparam DER output failed";

  // Validate it's actually DER format by parsing it
  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(bio) << "Cannot open DER output file";
  bssl::UniquePtr<DH> dh(d2i_DHparams_bio(bio.get(), nullptr));
  ASSERT_TRUE(dh) << "Output is not valid DER format";

  // Verify bit size
  const BIGNUM *p = DH_get0_p(dh.get());
  ASSERT_TRUE(p);
  ASSERT_EQ(512u, static_cast<unsigned>(BN_num_bits(p)))
      << "Wrong bit size in DER output";
}

// Test reading PEM parameters
TEST_F(DhparamTest, ReadPEMParameters) {
  // First generate parameters
  args_list_t gen_args = {"-out", in_path, "512"};
  ASSERT_TRUE(dhparamTool(gen_args));

  // Now read them back
  args_list_t read_args = {"-in", in_path, "-text", "-noout", "-out", out_path};
  EXPECT_TRUE(dhparamTool(read_args)) << "Failed to read PEM parameters";

  std::string output = ReadFileToString(out_path);
  EXPECT_NE(output.find("DH Parameters:"), std::string::npos);
}

// Test reading DER parameters
TEST_F(DhparamTest, ReadDERParameters) {
  // First generate DER parameters
  args_list_t gen_args = {"-outform", "DER", "-out", in_path, "512"};
  ASSERT_TRUE(dhparamTool(gen_args));

  // Now read them back
  args_list_t read_args = {"-inform", "DER",    "-in",  in_path,
                           "-text",   "-noout", "-out", out_path};
  EXPECT_TRUE(dhparamTool(read_args)) << "Failed to read DER parameters";

  std::string output = ReadFileToString(out_path);
  EXPECT_NE(output.find("DH Parameters:"), std::string::npos);
}

// Test format conversion: PEM to DER
TEST_F(DhparamTest, ConvertPEMtoDER) {
  // Generate PEM parameters
  args_list_t gen_args = {"-out", in_path, "512"};
  ASSERT_TRUE(dhparamTool(gen_args));

  // Convert to DER
  args_list_t convert_args = {"-in",      in_path, "-inform", "PEM",
                              "-outform", "DER",   "-out",    out_path};
  EXPECT_TRUE(dhparamTool(convert_args)) << "PEM to DER conversion failed";

  // Verify DER output
  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "rb"));
  ASSERT_TRUE(bio);
  bssl::UniquePtr<DH> dh(d2i_DHparams_bio(bio.get(), nullptr));
  ASSERT_TRUE(dh) << "Converted output is not valid DER";
}

// Test format conversion: DER to PEM
TEST_F(DhparamTest, ConvertDERtoPEM) {
  // Generate DER parameters
  args_list_t gen_args = {"-outform", "DER", "-out", in_path, "512"};
  ASSERT_TRUE(dhparamTool(gen_args));

  // Convert to PEM
  args_list_t convert_args = {"-in",      in_path, "-inform", "DER",
                              "-outform", "PEM",   "-out",    out_path};
  EXPECT_TRUE(dhparamTool(convert_args)) << "DER to PEM conversion failed";

  // Verify PEM output
  std::string output = ReadFileToString(out_path);
  EXPECT_NE(output.find("-----BEGIN DH PARAMETERS-----"), std::string::npos);
  EXPECT_NE(output.find("-----END DH PARAMETERS-----"), std::string::npos);

  bssl::UniquePtr<BIO> bio(BIO_new_file(out_path, "r"));
  ASSERT_TRUE(bio);
  bssl::UniquePtr<DH> dh(
      PEM_read_bio_DHparams(bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(dh) << "Converted output is not valid PEM";
}

// Test round-trip: generate -> save -> load -> verify
TEST_F(DhparamTest, RoundTrip) {
  // Generate and save
  args_list_t gen_args = {"-out", in_path, "512"};
  ASSERT_TRUE(dhparamTool(gen_args));

  // Load the original
  bssl::UniquePtr<BIO> bio1(BIO_new_file(in_path, "r"));
  ASSERT_TRUE(bio1);
  bssl::UniquePtr<DH> dh1(
      PEM_read_bio_DHparams(bio1.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(dh1);

  // Read and re-save
  args_list_t resave_args = {"-in", in_path, "-out", out_path};
  ASSERT_TRUE(dhparamTool(resave_args));

  // Load the re-saved version
  bssl::UniquePtr<BIO> bio2(BIO_new_file(out_path, "r"));
  ASSERT_TRUE(bio2);
  bssl::UniquePtr<DH> dh2(
      PEM_read_bio_DHparams(bio2.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(dh2);

  // Compare parameters
  const BIGNUM *p1 = DH_get0_p(dh1.get());
  const BIGNUM *p2 = DH_get0_p(dh2.get());
  const BIGNUM *g1 = DH_get0_g(dh1.get());
  const BIGNUM *g2 = DH_get0_g(dh2.get());

  ASSERT_EQ(0, BN_cmp(p1, p2)) << "Prime values don't match after round-trip";
  ASSERT_EQ(0, BN_cmp(g1, g2))
      << "Generator values don't match after round-trip";
}

// -------------------- Error Handling Tests ----------------------------------

class DhparamErrorTest : public ::testing::Test {
 protected:
  void SetUp() override { ASSERT_GT(createTempFILEpath(out_path), 0u); }

  void TearDown() override { RemoveFile(out_path); }

  char out_path[PATH_MAX];
};

// Test invalid bit size (too small)
TEST_F(DhparamErrorTest, InvalidBitSizeTooSmall) {
  args_list_t args = {"256"};
  EXPECT_FALSE(dhparamTool(args)) << "Should fail with bit size < 512";
}

// Test invalid bit size (non-numeric)
TEST_F(DhparamErrorTest, InvalidBitSizeNonNumeric) {
  args_list_t args = {"abc"};
  EXPECT_FALSE(dhparamTool(args)) << "Should fail with non-numeric bit size";
}

// Test invalid input format
TEST_F(DhparamErrorTest, InvalidInputFormat) {
  args_list_t args = {"-inform", "INVALID", "512"};
  EXPECT_FALSE(dhparamTool(args)) << "Should fail with invalid input format";
}

// Test invalid output format
TEST_F(DhparamErrorTest, InvalidOutputFormat) {
  args_list_t args = {"-outform", "INVALID", "512"};
  EXPECT_FALSE(dhparamTool(args)) << "Should fail with invalid output format";
}

// Test missing input file
TEST_F(DhparamErrorTest, MissingInputFile) {
  args_list_t args = {"-in", "/nonexistent/file.pem"};
  EXPECT_FALSE(dhparamTool(args)) << "Should fail with missing input file";
}

// Test conflicting options (both numbits and -in)
TEST_F(DhparamErrorTest, ConflictingOptions) {
  // Create a temp file for the test
  args_list_t gen_args = {"-out", out_path, "512"};
  ASSERT_TRUE(dhparamTool(gen_args));

  // Now try to use both numbits and -in
  args_list_t args = {"-in", out_path, "1024"};
  EXPECT_FALSE(dhparamTool(args))
      << "Should fail when both numbits and -in are specified";
}

// Test too many arguments
TEST_F(DhparamErrorTest, TooManyArguments) {
  args_list_t args = {"512", "1024"};
  EXPECT_FALSE(dhparamTool(args))
      << "Should fail with multiple numbits arguments";
}

// -------------------- OpenSSL Comparison Tests ------------------------------

// Parameterized tests for bit size generation comparison
class DhparamBitSizeComparisonTest
    : public ::testing::Test,
      public ::testing::WithParamInterface<BitSizeTestParams> {
 protected:
  void SetUp() override {
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                      "environment variables are not set";
    }
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
    }
  }

  const char *tool_executable_path;
  const char *openssl_executable_path;
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
};

TEST_P(DhparamBitSizeComparisonTest, CrossCompatibility) {
  const auto &params = GetParam();

  // Generate with AWS-LC
  std::string tool_command = std::string(tool_executable_path) +
                             " dhparam -out " + out_path_tool + " " +
                             std::to_string(params.numbits);
  ASSERT_EQ(system(tool_command.c_str()), 0) << "AWS-LC generation failed";

  // Verify OpenSSL can read AWS-LC generated parameters
  std::string openssl_read = std::string(openssl_executable_path) +
                             " dhparam -in " + out_path_tool + " -noout";
  ASSERT_EQ(system(openssl_read.c_str()), 0)
      << "OpenSSL cannot read AWS-LC generated parameters";

  // Generate with OpenSSL (can be slow, especially for larger sizes)
  std::string openssl_command = std::string(openssl_executable_path) +
                                " dhparam -out " + out_path_openssl + " " +
                                std::to_string(params.numbits);
  ASSERT_EQ(system(openssl_command.c_str()), 0) << "OpenSSL generation failed";

  // Verify AWS-LC can read OpenSSL generated parameters
  std::string tool_read = std::string(tool_executable_path) + " dhparam -in " +
                          out_path_openssl + " -noout";
  ASSERT_EQ(system(tool_read.c_str()), 0)
      << "AWS-LC cannot read OpenSSL generated parameters";
}

INSTANTIATE_TEST_SUITE_P(
    BitSizeTests, DhparamBitSizeComparisonTest,
    ::testing::Values(
        BitSizeTestParams{512, "Bits512"}, BitSizeTestParams{1024, "Bits1024"}
        // Note: 2048 is slow and may not be suitable for regular testing
        ),
    [](const ::testing::TestParamInfo<BitSizeTestParams> &info) {
      return info.param.test_name;
    });

// Additional specialized comparison tests
class DhparamComparisonTest : public ::testing::Test {
 protected:
  void SetUp() override {
    tool_executable_path = getenv("AWSLC_TOOL_PATH");
    openssl_executable_path = getenv("OPENSSL_TOOL_PATH");
    if (tool_executable_path == nullptr || openssl_executable_path == nullptr) {
      GTEST_SKIP() << "Skipping test: AWSLC_TOOL_PATH and/or OPENSSL_TOOL_PATH "
                      "environment variables are not set";
    }
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(params_path), 0u);
  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
      RemoveFile(params_path);
    }
  }

  const char *tool_executable_path;
  const char *openssl_executable_path;
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  char params_path[PATH_MAX];
};

// Test -noout flag comparison
TEST_F(DhparamComparisonTest, NooutComparison) {
  std::string tool_command = std::string(tool_executable_path) +
                             " dhparam -noout 512 > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " dhparam -noout 512 > " + out_path_openssl;

  ASSERT_EQ(system(tool_command.c_str()), 0);
  ASSERT_EQ(system(openssl_command.c_str()), 0);
  ASSERT_TRUE(ReadFileToString(out_path_tool).empty());
  ASSERT_TRUE(ReadFileToString(out_path_openssl).empty());
}

// Test DER format output comparison
TEST_F(DhparamComparisonTest, DERFormatComparison) {
  // Generate parameters
  std::string gen_command = std::string(tool_executable_path) +
                            " dhparam -out " + params_path + " 512";
  ASSERT_EQ(system(gen_command.c_str()), 0);

  // Convert to DER with both tools
  std::string tool_command = std::string(tool_executable_path) +
                             " dhparam -in " + params_path +
                             " -outform DER -out " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " dhparam -in " + params_path +
                                " -outform DER -out " + out_path_openssl;

  ASSERT_EQ(system(tool_command.c_str()), 0);
  ASSERT_EQ(system(openssl_command.c_str()), 0);

  // DER output should be byte-for-byte identical
  ASSERT_EQ(ReadFileToString(out_path_tool),
            ReadFileToString(out_path_openssl));
}

// Test PEM format round-trip compatibility
TEST_F(DhparamComparisonTest, PEMRoundTripCompatibility) {
  // Generate with AWS-LC
  std::string gen_command = std::string(tool_executable_path) +
                            " dhparam -out " + params_path + " 512";
  ASSERT_EQ(system(gen_command.c_str()), 0);

  // Read with OpenSSL and output
  std::string openssl_command = std::string(openssl_executable_path) +
                                " dhparam -in " + params_path + " -out " +
                                out_path_openssl;
  ASSERT_EQ(system(openssl_command.c_str()), 0);

  // Read OpenSSL output with AWS-LC
  std::string tool_command = std::string(tool_executable_path) +
                             " dhparam -in " + out_path_openssl + " -out " +
                             out_path_tool;
  ASSERT_EQ(system(tool_command.c_str()), 0);

  // Outputs should match (trimmed for whitespace differences)
  std::string tool_content = ReadFileToString(out_path_tool);
  std::string openssl_content = ReadFileToString(out_path_openssl);
  ASSERT_EQ(trim(tool_content), trim(openssl_content));
}

// Test text output format compatibility (structure only, not exact match)
TEST_F(DhparamComparisonTest, TextOutputStructure) {
  // Generate parameters
  std::string gen_command = std::string(tool_executable_path) +
                            " dhparam -out " + params_path + " 512";
  ASSERT_EQ(system(gen_command.c_str()), 0);

  // Get text output from both tools
  std::string tool_command = std::string(tool_executable_path) +
                             " dhparam -in " + params_path +
                             " -text -noout > " + out_path_tool;
  std::string openssl_command = std::string(openssl_executable_path) +
                                " dhparam -in " + params_path +
                                " -text -noout > " + out_path_openssl;

  ASSERT_EQ(system(tool_command.c_str()), 0);
  ASSERT_EQ(system(openssl_command.c_str()), 0);

  std::string tool_content = ReadFileToString(out_path_tool);
  std::string openssl_content = ReadFileToString(out_path_openssl);

  // Both should contain key structural elements
  EXPECT_NE(tool_content.find("DH Parameters:"), std::string::npos);
  EXPECT_NE(tool_content.find("512 bit"), std::string::npos);
  EXPECT_NE(tool_content.find("P:"), std::string::npos);
  EXPECT_NE(tool_content.find("G:"), std::string::npos);

  EXPECT_NE(openssl_content.find("DH Parameters:"), std::string::npos);
  EXPECT_NE(openssl_content.find("512 bit"), std::string::npos);
  // OpenSSL formats P differently but should still contain it
}

// Test format conversion compatibility
TEST_F(DhparamComparisonTest, FormatConversionCompatibility) {
  // Generate PEM with AWS-LC
  std::string gen_command = std::string(tool_executable_path) +
                            " dhparam -out " + params_path + " 512";
  ASSERT_EQ(system(gen_command.c_str()), 0);

  // Convert PEM to DER with AWS-LC
  std::string awslc_convert = std::string(tool_executable_path) +
                              " dhparam -in " + params_path +
                              " -outform DER -out " + out_path_tool;
  ASSERT_EQ(system(awslc_convert.c_str()), 0);

  // Convert same PEM to DER with OpenSSL
  std::string openssl_convert = std::string(openssl_executable_path) +
                                " dhparam -in " + params_path +
                                " -outform DER -out " + out_path_openssl;
  ASSERT_EQ(system(openssl_convert.c_str()), 0);

  // DER outputs should be identical
  ASSERT_EQ(ReadFileToString(out_path_tool),
            ReadFileToString(out_path_openssl));
}

}  // namespace
