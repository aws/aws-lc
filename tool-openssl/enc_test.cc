// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/pem.h>
#include <sys/stat.h>
#include <cctype>
#if !defined(OPENSSL_WINDOWS)
#include <signal.h>
#include <sys/resource.h>
#include <unistd.h>
#endif
#include "internal.h"
#include "test_util.h"

struct EncCipherTestCase {
  const char *flag;
  size_t key_len;
  size_t iv_len;
  size_t block_len;
  bool needs_legacy_provider;
};

static const EncCipherTestCase kEncCipherTestCases[] = {
    {"-aes-128-cbc", 16, 16, 16, false}, {"-aes-128-cfb", 16, 16, 16, false},
    {"-aes-128-ctr", 16, 16, 16, false}, {"-aes-128-ecb", 16, 0, 16, false},
    {"-aes-128-ofb", 16, 16, 16, false}, {"-aes-192-cbc", 24, 16, 16, false},
    {"-aes-192-cfb", 24, 16, 16, false}, {"-aes-192-ctr", 24, 16, 16, false},
    {"-aes-192-ecb", 24, 0, 16, false},  {"-aes-192-ofb", 24, 16, 16, false},
    {"-aes-256-cbc", 32, 16, 16, false}, {"-aes-256-cfb", 32, 16, 16, false},
    {"-aes-256-ctr", 32, 16, 16, false}, {"-aes-256-ecb", 32, 0, 16, false},
    {"-aes-256-ofb", 32, 16, 16, false}, {"-aes128", 16, 16, 16, false},
    {"-aes256", 32, 16, 16, false},      {"-des-cbc", 8, 8, 8, true},
    {"-des-ede3-cbc", 24, 8, 8, false},
};

static args_list_t EncArgs(const EncCipherTestCase &cipher, bool decrypt,
                           const std::string &in_path,
                           const std::string &out_path) {
  args_list_t args = {decrypt ? "-d" : "-e", cipher.flag, "-K",
                      std::string(cipher.key_len * 2, '1')};
  if (cipher.iv_len != 0) {
    args.push_back("-iv");
    args.push_back(std::string(cipher.iv_len * 2, '2'));
  }
  args.push_back("-in");
  args.push_back(in_path);
  args.push_back("-out");
  args.push_back(out_path);
  return args;
}

static std::string EncCommand(const char *executable,
                              const EncCipherTestCase &cipher, bool decrypt,
                              const std::string &in_path,
                              const std::string &out_path,
                              bool load_legacy_provider) {
  std::string command = ShellEscape(executable) + " enc";
  if (load_legacy_provider && cipher.needs_legacy_provider) {
    command += " -provider default -provider legacy";
  }
  for (const auto &arg : EncArgs(cipher, decrypt, in_path, out_path)) {
    command += " " + ShellEscape(arg);
  }
  return command;
}

// Reports whether |executable| is OpenSSL 3.x or later. `list -providers` only
// exists in 3.x, so probe for it rather than relying on OPENSSL_TOOL_VERSION,
// which is unset in local runs.
static bool IsOpenSSL3OrLater(const char *executable) {
#if defined(OPENSSL_WINDOWS)
  const char *null_device = "NUL";
#else
  const char *null_device = "/dev/null";
#endif
  return ExecuteCommandExitCode(ShellEscape(executable) +
                                " list -providers > " + null_device +
                                " 2>&1") == 0;
}

static void WriteInput(const char *path, size_t len) {
  ScopedFILE file(fopen(path, "wb"));
  ASSERT_TRUE(file);
  for (size_t i = 0; i < len; i++) {
    const uint8_t byte = static_cast<uint8_t>(i);
    ASSERT_EQ(fwrite(&byte, 1, 1, file.get()), 1u);
  }
}

class EncTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);

    // Create test input file with sample data
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    const char *test_data = "Hello, World! This is test data for encryption.";
    fwrite(test_data, 1, strlen(test_data), in_file.get());
  }

  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
  }

  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
};

// -------------------- Enc Basic Functionality Tests -------------------------

// Test help option
TEST_F(EncTest, Help) {
  args_list_t args = {"-help"};
  int result = encTool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test basic encryption with AES-128-CBC
TEST_F(EncTest, BasicEncryption) {
  args_list_t args = {"-e",   "-aes-128-cbc",
                      "-K",   "0123456789abcdef0123456789abcdef",
                      "-iv",  "0123456789abcdef0123456789abcdef",
                      "-in",  in_path,
                      "-out", out_path};
  int result = encTool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Verify output file exists and has content
  struct stat st;
  ASSERT_EQ(stat(out_path, &st), 0);
  ASSERT_GT(st.st_size, 0);
}

// Test basic decryption with AES-128-CBC
TEST_F(EncTest, BasicDecryption) {
  // First encrypt
  args_list_t encrypt_args = {"-e",   "-aes-128-cbc",
                              "-K",   "0123456789abcdef0123456789abcdef",
                              "-iv",  "0123456789abcdef0123456789abcdef",
                              "-in",  in_path,
                              "-out", out_path};
  int result = encTool(encrypt_args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Create temp file for decrypted output
  char decrypt_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(decrypt_path), 0u);

  // Then decrypt
  args_list_t decrypt_args = {"-d",   "-aes-128-cbc",
                              "-K",   "0123456789abcdef0123456789abcdef",
                              "-iv",  "0123456789abcdef0123456789abcdef",
                              "-in",  out_path,
                              "-out", decrypt_path};
  result = encTool(decrypt_args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Verify decrypted content matches original
  std::string original = ReadFileToString(in_path);
  std::string decrypted = ReadFileToString(decrypt_path);
  ASSERT_EQ(original, decrypted);

  RemoveFile(decrypt_path);
}

// Test decryption with explicit -d flag
TEST_F(EncTest, ExplicitDecryption) {
  // First encrypt
  args_list_t encrypt_args = {"-e",   "-aes-128-cbc",
                              "-K",   "0123456789abcdef0123456789abcdef",
                              "-iv",  "0123456789abcdef0123456789abcdef",
                              "-in",  in_path,
                              "-out", out_path};
  int result = encTool(encrypt_args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Create temp file for decrypted output
  char decrypt_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(decrypt_path), 0u);

  // Test explicit -d flag
  args_list_t decrypt_args = {"-d",   "-aes-128-cbc",
                              "-K",   "0123456789abcdef0123456789abcdef",
                              "-iv",  "0123456789abcdef0123456789abcdef",
                              "-in",  out_path,
                              "-out", decrypt_path};
  result = encTool(decrypt_args);
  ASSERT_EQ(kToolExitSuccess, result);

  RemoveFile(decrypt_path);
}

TEST_F(EncTest, NoCipherCopiesInput) {
  const std::vector<args_list_t> options = {{},
                                            {"-d"},
                                            {"-e"},
                                            {"-K", "invalid", "-iv", "invalid"},
                                            {"-aes-256-cbc", "-none"}};
  for (size_t len : {0u, 16u, 1024u, 1025u}) {
    WriteInput(in_path, len);
    for (const auto &flags : options) {
      args_list_t args = {"-in", in_path, "-out", out_path};
      args.insert(args.end(), flags.begin(), flags.end());
      ASSERT_EQ(kToolExitSuccess, encTool(args));
      EXPECT_EQ(ReadFileToString(in_path), ReadFileToString(out_path));
    }
  }
}

// Test encryption without -e flag (should default to encrypt)
TEST_F(EncTest, DefaultEncrypt) {
  args_list_t args = {"-aes-128-cbc",
                      "-K",
                      "0123456789abcdef0123456789abcdef",
                      "-iv",
                      "0123456789abcdef0123456789abcdef",
                      "-in",
                      in_path,
                      "-out",
                      out_path};
  int result = encTool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

TEST_F(EncTest, RegisteredCiphersRoundTrip) {
  char encrypted_path[PATH_MAX];
  char decrypted_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(encrypted_path), 0u);
  ASSERT_GT(createTempFILEpath(decrypted_path), 0u);

  for (const auto &cipher : kEncCipherTestCases) {
    SCOPED_TRACE(cipher.flag);
    ASSERT_EQ(kToolExitSuccess,
              encTool(EncArgs(cipher, false, in_path, encrypted_path)));
    ASSERT_EQ(kToolExitSuccess,
              encTool(EncArgs(cipher, true, encrypted_path, decrypted_path)));
    EXPECT_EQ(ReadFileToString(in_path), ReadFileToString(decrypted_path));
  }

  RemoveFile(encrypted_path);
  RemoveFile(decrypted_path);
}

// -------------------- Enc Option Usage Error Tests --------------------------

class EncOptionUsageErrorsTest : public EncTest {
 protected:
  void TestOptionUsageErrors(const std::vector<std::string> &args) {
    args_list_t c_args;
    for (const auto &arg : args) {
      c_args.push_back(arg.c_str());
    }
    int result = encTool(c_args);
    ASSERT_EQ(kToolExitFailure, result);
  }
};

// Test missing required key
TEST_F(EncOptionUsageErrorsTest, MissingKey) {
  std::vector<std::vector<std::string>> testparams = {
      {"-e", "-aes-128-cbc", "-iv", "0123456789abcdef0123456789abcdef", "-in",
       in_path},
      {"-d", "-aes-128-cbc", "-iv", "0123456789abcdef0123456789abcdef", "-in",
       in_path},
      {"-aes-128-cbc", "-iv", "0123456789abcdef0123456789abcdef", "-in",
       in_path}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

TEST_F(EncTest, LastOptionsWin) {
  char encrypted_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(encrypted_path), 0u);
  const std::string key(64, '1'), iv(32, '2');
  ASSERT_EQ(kToolExitSuccess,
            encTool({"-none",   "-aes-128-cbc", "-aes-256-cbc",
                     "-d",      "-e",           "-K",
                     "invalid", "-K",           key,
                     "-iv",     "invalid",      "-iv",
                     iv,        "-in",          "missing.pem",
                     "-in",     in_path,        "-out",
                     "",        "-out",         encrypted_path}));
  const std::string encrypted = ReadFileToString(encrypted_path);
  ASSERT_EQ(kToolExitSuccess, encTool({"-aes-256-cbc", "-K", key, "-iv", iv,
                                       "-in", in_path, "-out", out_path}));
  EXPECT_EQ(encrypted, ReadFileToString(out_path));
  ASSERT_EQ(kToolExitSuccess,
            encTool({"-aes-256-cbc", "-e", "-d", "-K", key, "-iv", iv, "-in",
                     encrypted_path, "-out", out_path}));
  EXPECT_EQ(ReadFileToString(in_path), ReadFileToString(out_path));
  RemoveFile(encrypted_path);
}

// Test invalid hex key
TEST_F(EncOptionUsageErrorsTest, InvalidHexKey) {
  std::vector<std::vector<std::string>> testparams = {
      {"-e", "-aes-128-cbc", "-K", "invalidhexkey", "-iv",
       "0123456789abcdef0123456789abcdef", "-in", in_path},
      {"-e", "-aes-128-cbc", "-K", "0123456789abcdefg123456789abcdef", "-iv",
       "0123456789abcdef0123456789abcdef", "-in", in_path}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test invalid hex IV
TEST_F(EncOptionUsageErrorsTest, InvalidHexIV) {
  std::vector<std::vector<std::string>> testparams = {
      {"-e", "-aes-128-cbc", "-K", "0123456789abcdef0123456789abcdef", "-iv",
       "invalidhexiv", "-in", in_path},
      {"-e", "-aes-128-cbc", "-K", "0123456789abcdef0123456789abcdef", "-iv",
       "0123456789abcdefg123456789abcdef", "-in", in_path}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

TEST_F(EncTest, HexValuesArePaddedAndTruncated) {
  for (const char *option : {"-K", "-iv"}) {
    const size_t width = strcmp(option, "-K") == 0 ? 64 : 32;
    for (const std::string &value :
         {std::string(), std::string("f"), std::string("aBc"),
          std::string(width - 1, '1'), std::string(width, '1') + "not-hex"}) {
      SCOPED_TRACE(std::string(option) + "=" + value);
      args_list_t args = {"-aes-256-cbc",
                          "-K",
                          std::string(64, '0'),
                          "-iv",
                          std::string(32, '0'),
                          "-in",
                          in_path,
                          "-out",
                          out_path,
                          option,
                          value};
      testing::internal::CaptureStderr();
      const int result = encTool(args);
      const std::string errors = testing::internal::GetCapturedStderr();
      ASSERT_EQ(kToolExitSuccess, result) << errors;
      EXPECT_NE(std::string::npos,
                errors.find(value.size() < width ? "padding with zero bytes"
                                                 : "ignoring excess"));
      const std::string ciphertext = ReadFileToString(out_path);
      std::string normalized = value;
      normalized.resize(width, '0');
      args.back() = normalized;
      ASSERT_EQ(kToolExitSuccess, encTool(args));
      EXPECT_EQ(ciphertext, ReadFileToString(out_path));
    }
  }
}

TEST_F(EncTest, NoPadding) {
  for (size_t len : {0u, 16u, 17u, 1024u, 1025u}) {
    SCOPED_TRACE(len);
    WriteInput(in_path, len);
    args_list_t args = {"-aes-256-cbc", "-nopad",
                        "-K",           std::string(64, '1'),
                        "-iv",          std::string(32, '2'),
                        "-in",          in_path,
                        "-out",         out_path};
    EXPECT_EQ(len % 16 == 0 ? kToolExitSuccess : kToolExitFailure,
              encTool(args));
    if (len % 16 != 0) {
      continue;
    }
    EXPECT_EQ(len, ReadFileToString(out_path).size());
    args = {"-aes-256-cbc",
            "-nopad",
            "-d",
            "-K",
            std::string(64, '1'),
            "-iv",
            std::string(32, '2'),
            "-in",
            out_path,
            "-out",
            in_path};
    ASSERT_EQ(kToolExitSuccess, encTool(args));
    std::string expected;
    for (size_t i = 0; i < len; i++) {
      expected.push_back(static_cast<char>(i));
    }
    EXPECT_EQ(expected, ReadFileToString(in_path));
  }
}

#if !defined(OPENSSL_WINDOWS)
TEST_F(EncTest, BufferedOutputFailureIsReported) {
  // Limit file writes in a child process so the limit and signal disposition
  // cannot leak into other tests. A small output is buffered until flush.
  for (const char *cipher : {"-none", "-aes-256-cbc"}) {
    SCOPED_TRACE(cipher);
    ASSERT_EXIT(
        {
          struct rlimit limit;
          limit.rlim_cur = 0;
          limit.rlim_max = 0;
          if (setrlimit(RLIMIT_FSIZE, &limit) != 0 ||
              signal(SIGXFSZ, SIG_IGN) == SIG_ERR) {
            _exit(2);
          }
          _exit(encTool({cipher, "-K", std::string(64, '1'), "-iv",
                         std::string(32, '2'), "-in", in_path, "-out",
                         out_path}));
        },
        // gtest captures stderr in a file, which is also subject to the limit.
        testing::ExitedWithCode(kToolExitFailure), "");
  }
}
#endif

// Test missing IV for cipher that requires it
TEST_F(EncOptionUsageErrorsTest, MissingIV) {
  std::vector<std::vector<std::string>> testparams = {
      {"-e", "-aes-128-cbc", "-K", "0123456789abcdef0123456789abcdef", "-in",
       in_path}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// Test invalid input file
TEST_F(EncOptionUsageErrorsTest, InvalidInputFile) {
  std::vector<std::vector<std::string>> testparams = {
      {"-e", "-aes-128-cbc", "-K", "0123456789abcdef0123456789abcdef", "-iv",
       "0123456789abcdef0123456789abcdef", "-in", "/nonexistent/file.txt"}};
  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// -------------------- Enc OpenSSL Comparison Tests --------------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class EncComparisonTest : public ::testing::Test {
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
    ASSERT_GT(createTempFILEpath(out_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(out_path_openssl), 0u);

    // Create test input file
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    const char *test_data =
        "Hello, World! This is test data for encryption comparison.";
    fwrite(test_data, 1, strlen(test_data), in_file.get());
  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(in_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
    }
  }

  char in_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  const char *tool_executable_path;
  const char *openssl_executable_path;
};

// Test encryption comparison with OpenSSL
TEST_F(EncComparisonTest, EncryptionComparison) {
  std::string key = "0123456789abcdef0123456789abcdef";
  std::string iv = "0123456789abcdef0123456789abcdef";

  std::string tool_command = ShellEscape(tool_executable_path) +
                             " enc -e -aes-128-cbc -K " + ShellEscape(key) +
                             " -iv " + ShellEscape(iv) + " -in " +
                             ShellEscape(in_path) + " -out " +
                             ShellEscape(out_path_tool);
  std::string openssl_command =
      ShellEscape(openssl_executable_path) + " enc -e -aes-128-cbc -K " +
      ShellEscape(key) + " -iv " + ShellEscape(iv) + " -in " +
      ShellEscape(in_path) + " -out " + ShellEscape(out_path_openssl);

  std::string tool_output_str, openssl_output_str;
  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  // Compare encrypted outputs
  ASSERT_EQ(tool_output_str, openssl_output_str);
}

// Test decryption comparison with OpenSSL
TEST_F(EncComparisonTest, DecryptionComparison) {
  std::string key = "0123456789abcdef0123456789abcdef";
  std::string iv = "0123456789abcdef0123456789abcdef";

  // First encrypt with OpenSSL to create encrypted data
  char encrypted_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(encrypted_path), 0u);

  std::string openssl_encrypt_cmd =
      ShellEscape(openssl_executable_path) + " enc -e -aes-128-cbc -K " +
      ShellEscape(key) + " -iv " + ShellEscape(iv) + " -in " +
      ShellEscape(in_path) + " -out " + ShellEscape(encrypted_path);
  ASSERT_EQ(ExecuteCommand(openssl_encrypt_cmd), 0);

  // Now test decryption comparison
  std::string tool_command =
      ShellEscape(tool_executable_path) + " enc -d -aes-128-cbc -K " +
      ShellEscape(key) + " -iv " + ShellEscape(iv) + " -in " +
      ShellEscape(encrypted_path) + " -out " + ShellEscape(out_path_tool);
  std::string openssl_command =
      ShellEscape(openssl_executable_path) + " enc -d -aes-128-cbc -K " +
      ShellEscape(key) + " -iv " + ShellEscape(iv) + " -in " +
      ShellEscape(encrypted_path) + " -out " + ShellEscape(out_path_openssl);

  std::string tool_output_str, openssl_output_str;
  RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                              out_path_openssl, tool_output_str,
                              openssl_output_str);

  // Compare decrypted outputs
  ASSERT_EQ(tool_output_str, openssl_output_str);

  RemoveFile(encrypted_path);
}

// "-" selects stdin for -in and stdout for -out, as in OpenSSL.
TEST_F(EncComparisonTest, DashMeansStdio) {
  const std::string args =
      " enc -e -aes-128-cbc -K 0123456789abcdef0123456789abcdef"
      " -iv 0123456789abcdef0123456789abcdef -in - -out - < " +
      ShellEscape(in_path);
  std::string tool_output_str, openssl_output_str;
  RunCommandsAndCompareOutput(ShellEscape(tool_executable_path) + args + " > " +
                                  ShellEscape(out_path_tool),
                              ShellEscape(openssl_executable_path) + args +
                                  " > " + ShellEscape(out_path_openssl),
                              out_path_tool, out_path_openssl, tool_output_str,
                              openssl_output_str);
  EXPECT_FALSE(tool_output_str.empty());
  EXPECT_EQ(tool_output_str, openssl_output_str);
}

TEST_F(EncComparisonTest, OptionSemanticsMatchOpenSSL) {
  const std::string key(64, '1'), iv(32, '2');
  struct Case {
    args_list_t options;
    size_t len;
    bool success;
  };
  const Case cases[] = {
      {{}, 1025, true},
      {{"-d", "-K", "invalid", "-iv", "invalid"}, 17, true},
      {{"-none", "-aes-256-cbc", "-K", key, "-iv", iv}, 17, true},
      {{"-aes-256-cbc", "-d", "-e", "-K", key, "-iv", iv}, 17, true},
      {{"-aes-256-cbc", "-K", "", "-iv", ""}, 17, true},
      {{"-aes-256-cbc", "-K", "f", "-iv", "aBc"}, 17, true},
      {{"-aes-256-cbc", "-K", key + "not-hex", "-iv", iv + "not-hex"},
       17,
       true},
      {{"-aes-256-cbc", "-K", "invalid", "-K", key, "-iv", "invalid", "-iv",
        iv},
       17,
       true},
      {{"-aes-256-cbc", "-K", "invalid", "-iv", iv}, 17, false},
      {{"-aes-256-cbc", "-nopad", "-K", key, "-iv", iv}, 16, true},
      {{"-aes-256-cbc", "-nopad", "-K", key, "-iv", iv}, 17, false},
      {{"-aes-256-cbc", "-nopad", "-e", "-d", "-K", key, "-iv", iv}, 16, true},
      {{"-aes-256-ecb", "-K", key, "-iv", "invalid"}, 17, true},
  };
  for (const auto &test : cases) {
    WriteInput(in_path, test.len);
    std::string options = " enc";
    for (const auto &option : test.options) {
      options += " " + ShellEscape(option);
    }
    SCOPED_TRACE(options);
    // Exercise last-wins for filenames without touching the earlier paths.
    options += " -in missing.pem -in " + ShellEscape(in_path) + " -out " +
               ShellEscape("");
    const int tool_result =
        ExecuteCommandExitCode(ShellEscape(tool_executable_path) + options +
                               " -out " + ShellEscape(out_path_tool));
    const int openssl_result =
        ExecuteCommandExitCode(ShellEscape(openssl_executable_path) + options +
                               " -out " + ShellEscape(out_path_openssl));
    EXPECT_EQ(test.success ? 0 : 1, tool_result);
    EXPECT_EQ(openssl_result, tool_result);
    if (test.success) {
      EXPECT_EQ(ReadFileToString(out_path_openssl),
                ReadFileToString(out_path_tool));
    }
  }
}

// As in OpenSSL 1.1.1, the last cipher option, including -none, wins. OpenSSL
// 3.x differs: it resolves the cipher after parsing, so -none after a cipher
// has no effect (and enc prompts for a password), and newer releases reject
// multiple ciphers. Compare against OpenSSL only for 1.1.1.
TEST_F(EncComparisonTest, LastCipherOptionWinsLikeOpenSSL111) {
  const std::string key_iv =
      " -K " + std::string(64, '1') + " -iv " + std::string(32, '2');
  struct Case {
    std::string options;
    // Options that should give the same output from our tool.
    std::string equivalent;
  };
  const Case cases[] = {
      {" -aes-256-cbc -none", " -none"},
      {" -aes-128-cbc -aes-256-cbc" + key_iv, " -aes-256-cbc" + key_iv},
  };
  const bool compare_openssl = !IsOpenSSL3OrLater(openssl_executable_path);
  WriteInput(in_path, 17);
  const std::string io = " -in " + ShellEscape(in_path) + " -out ";
  for (const auto &test : cases) {
    SCOPED_TRACE(test.options);
    ASSERT_EQ(kToolExitSuccess,
              ExecuteCommandExitCode(ShellEscape(tool_executable_path) +
                                     " enc" + test.equivalent + io +
                                     ShellEscape(out_path_openssl)));
    const std::string expected = ReadFileToString(out_path_openssl);
    ASSERT_EQ(
        kToolExitSuccess,
        ExecuteCommandExitCode(ShellEscape(tool_executable_path) + " enc" +
                               test.options + io + ShellEscape(out_path_tool)));
    EXPECT_EQ(expected, ReadFileToString(out_path_tool));

    if (compare_openssl) {
      ASSERT_EQ(0, ExecuteCommandExitCode(ShellEscape(openssl_executable_path) +
                                          " enc" + test.options + io +
                                          ShellEscape(out_path_openssl)));
      EXPECT_EQ(ReadFileToString(out_path_openssl),
                ReadFileToString(out_path_tool));
    }
  }
}

TEST_F(EncComparisonTest, RegisteredCiphersMatchOpenSSL) {
  char decrypted_path_tool[PATH_MAX];
  char decrypted_path_openssl[PATH_MAX];
  ASSERT_GT(createTempFILEpath(decrypted_path_tool), 0u);
  ASSERT_GT(createTempFILEpath(decrypted_path_openssl), 0u);

  // OpenSSL 3.x moved DES-CBC to the legacy provider.
  const bool load_legacy_provider = IsOpenSSL3OrLater(openssl_executable_path);

  for (const auto &cipher : kEncCipherTestCases) {
    const size_t input_lengths[] = {0, cipher.block_len, cipher.block_len + 1};
    for (size_t input_len : input_lengths) {
      SCOPED_TRACE(std::string(cipher.flag) + ", input length " +
                   std::to_string(input_len));
      WriteInput(in_path, input_len);

      std::string tool_command = EncCommand(tool_executable_path, cipher, false,
                                            in_path, out_path_tool, false);
      std::string openssl_command =
          EncCommand(openssl_executable_path, cipher, false, in_path,
                     out_path_openssl, load_legacy_provider);
      std::string tool_output_str, openssl_output_str;
      RunCommandsAndCompareOutput(tool_command, openssl_command, out_path_tool,
                                  out_path_openssl, tool_output_str,
                                  openssl_output_str);
      EXPECT_EQ(tool_output_str, openssl_output_str);

      tool_command = EncCommand(tool_executable_path, cipher, true,
                                out_path_openssl, decrypted_path_tool, false);
      openssl_command =
          EncCommand(openssl_executable_path, cipher, true, out_path_openssl,
                     decrypted_path_openssl, load_legacy_provider);
      RunCommandsAndCompareOutput(tool_command, openssl_command,
                                  decrypted_path_tool, decrypted_path_openssl,
                                  tool_output_str, openssl_output_str);
      EXPECT_EQ(tool_output_str, openssl_output_str);
      EXPECT_EQ(ReadFileToString(in_path), tool_output_str);
    }
  }

  RemoveFile(decrypted_path_tool);
  RemoveFile(decrypted_path_openssl);
}
