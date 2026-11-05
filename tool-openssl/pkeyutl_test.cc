// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <cctype>
#if !defined(OPENSSL_WINDOWS)
#include <signal.h>
#include <unistd.h>
#endif
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"

class PKeyUtlTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(sig_path), 0u);
    ASSERT_GT(createTempFILEpath(key_path), 0u);
    ASSERT_GT(createTempFILEpath(pubkey_path), 0u);
    ASSERT_GT(createTempFILEpath(protected_key_path), 0u);

    // Create and save a private key in PEM format
    bssl::UniquePtr<EVP_PKEY> pkey(CreateTestKey(2048));
    ASSERT_TRUE(pkey);

    ScopedFILE key_file(fopen(key_path, "wb"));
    ASSERT_TRUE(key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(key_file.get(), pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));

    // Create a public key file
    ScopedFILE pubkey_file(fopen(pubkey_path, "wb"));
    ASSERT_TRUE(pubkey_file);
    ASSERT_TRUE(PEM_write_PUBKEY(pubkey_file.get(), pkey.get()));

    // Create a password-protected private key
    ScopedFILE protected_key_file(fopen(protected_key_path, "wb"));
    ASSERT_TRUE(protected_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(
        protected_key_file.get(), pkey.get(), EVP_aes_256_cbc(),
        (unsigned char *)"testpassword", 12, nullptr, nullptr));

    // Create a test input file with some data
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    const char *test_data = "Test data for signing and verification";
    ASSERT_EQ(fwrite(test_data, 1, strlen(test_data), in_file.get()),
              strlen(test_data));
  }

  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
    RemoveFile(sig_path);
    RemoveFile(key_path);
    RemoveFile(pubkey_path);
    RemoveFile(protected_key_path);
  }

  void SignExpectSuccess() {
    args_list_t args = {"-sign", "-inkey", key_path, "-in",
                        in_path, "-out",   sig_path};
    ASSERT_EQ(kToolExitSuccess, pkeyutlTool(args));
  }

  void VerifyExpectSuccess(const args_list_t &key_args) {
    args_list_t args = {"-verify", "-in",  in_path, "-sigfile",
                        sig_path,  "-out", out_path};
    args.insert(args.end(), key_args.begin(), key_args.end());
    ASSERT_EQ(kToolExitSuccess, pkeyutlTool(args));
    EXPECT_NE(
        ReadFileToString(out_path).find("Signature Verified Successfully"),
        std::string::npos);
  }

  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  char sig_path[PATH_MAX];
  char key_path[PATH_MAX];
  char pubkey_path[PATH_MAX];
  char protected_key_path[PATH_MAX];
};

// ------------------------ PKeyUtl Option Tests -------------------------

// Test basic signing operation
TEST_F(PKeyUtlTest, Sign) {
  args_list_t args = {"-sign", "-inkey", key_path, "-in",
                      in_path, "-out",   out_path};
  int result = pkeyutlTool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Verify the signature file was created and has content
  struct stat st;
  ASSERT_EQ(stat(out_path, &st), 0);
  ASSERT_GT(st.st_size, 0);
}

// Test basic verification operation
TEST_F(PKeyUtlTest, Verify) {
  // First sign the data
  {
    args_list_t args = {"-sign", "-inkey", key_path, "-in",
                        in_path, "-out",   sig_path};
    int result = pkeyutlTool(args);
    ASSERT_EQ(kToolExitSuccess, result);
  }

  // Then verify the signature
  {
    args_list_t args = {"-verify", "-pubin",   "-inkey", pubkey_path, "-in",
                        in_path,   "-sigfile", sig_path, "-out",      out_path};
    int result = pkeyutlTool(args);
    ASSERT_EQ(kToolExitSuccess, result);

    // Check that the output contains "Signature Verified Successfully"
    std::string output = ReadFileToString(out_path);
    ASSERT_NE(output.find("Signature Verified Successfully"),
              std::string::npos);
  }
}

TEST_F(PKeyUtlTest, EncryptDecrypt) {
  args_list_t encrypt_args = {"-encrypt", "-pubin", "-inkey", pubkey_path,
                              "-in",      in_path,  "-out",   out_path};
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(encrypt_args));

  char decrypted_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(decrypted_path), 0u);
  args_list_t decrypt_args = {"-decrypt", "-inkey", key_path,      "-in",
                              out_path,   "-out",   decrypted_path};
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(decrypt_args));
  EXPECT_EQ(ReadFileToString(in_path), ReadFileToString(decrypted_path));
  RemoveFile(decrypted_path);
}

TEST_F(PKeyUtlTest, EncryptDecryptOaep) {
  args_list_t encrypt_args = {
      "-encrypt", "-pubin",
      "-inkey",   pubkey_path,
      "-in",      in_path,
      "-pkeyopt", "rsa_padding_mode:oaep",
      "-pkeyopt", "rsa_oaep_md:sha256",
      "-pkeyopt", "rsa_mgf1_md:sha256",
      "-out",     out_path,
  };
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(encrypt_args));

  char decrypted_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(decrypted_path), 0u);
  args_list_t decrypt_args = {
      "-decrypt",
      "-inkey",
      key_path,
      "-in",
      out_path,
      "-pkeyopt",
      "rsa_padding_mode:oaep",
      "-pkeyopt",
      "rsa_oaep_md:sha256",
      "-pkeyopt",
      "rsa_mgf1_md:sha256",
      "-out",
      decrypted_path,
  };
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(decrypt_args));
  EXPECT_EQ(ReadFileToString(in_path), ReadFileToString(decrypted_path));
  RemoveFile(decrypted_path);
}

TEST_F(PKeyUtlTest, DecryptWithEncryptedPrivateKey) {
  args_list_t encrypt_args = {"-encrypt", "-pubin", "-inkey", pubkey_path,
                              "-in",      in_path,  "-out",   out_path};
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(encrypt_args));

  char decrypted_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(decrypted_path), 0u);
  args_list_t decrypt_args = {
      "-decrypt",          "-inkey", protected_key_path, "-passin",
      "pass:testpassword", "-in",    out_path,           "-out",
      decrypted_path};
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(decrypt_args));
  EXPECT_EQ(ReadFileToString(in_path), ReadFileToString(decrypted_path));
  RemoveFile(decrypted_path);
}

TEST_F(PKeyUtlTest, DecryptWithWrongKeyFails) {
  args_list_t encrypt_args = {"-encrypt", "-pubin", "-inkey", pubkey_path,
                              "-in",      in_path,  "-out",   out_path};
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(encrypt_args));

  char wrong_key_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(wrong_key_path), 0u);
  bssl::UniquePtr<EVP_PKEY> wrong_key(CreateTestKey(2048));
  ASSERT_TRUE(wrong_key);
  {
    ScopedFILE wrong_key_file(fopen(wrong_key_path, "wb"));
    ASSERT_TRUE(wrong_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(wrong_key_file.get(), wrong_key.get(),
                                     nullptr, nullptr, 0, nullptr, nullptr));
  }

  args_list_t decrypt_args = {"-decrypt", "-inkey", wrong_key_path, "-in",
                              out_path,   "-out",   sig_path};
  EXPECT_EQ(kToolExitFailure, pkeyutlTool(decrypt_args));
  RemoveFile(wrong_key_path);
}

// A signature that does not match the input exits nonzero.
TEST_F(PKeyUtlTest, VerifyFailureExitCode) {
  {
    args_list_t args = {"-sign", "-inkey", key_path, "-in",
                        in_path, "-out",   sig_path};
    ASSERT_EQ(kToolExitSuccess, pkeyutlTool(args));
  }

  // Tamper with the signed data so verification fails.
  {
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    const char *tampered = "Different data that was never signed";
    ASSERT_EQ(fwrite(tampered, 1, strlen(tampered), in_file.get()),
              strlen(tampered));
  }

  args_list_t args = {"-verify", "-pubin",   "-inkey", pubkey_path, "-in",
                      in_path,   "-sigfile", sig_path, "-out",      out_path};
  ASSERT_EQ(kToolExitFailure, pkeyutlTool(args));

  std::string output = ReadFileToString(out_path);
  ASSERT_NE(output.find("Signature Verification Failure"), std::string::npos);
}

// Test basic passin integration with password-protected key
TEST_F(PKeyUtlTest, PassinBasicIntegration) {
  args_list_t args = {"-sign",
                      "-inkey",
                      protected_key_path,
                      "-passin",
                      "pass:testpassword",
                      "-in",
                      in_path,
                      "-out",
                      out_path};
  int result = pkeyutlTool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  struct stat st;
  ASSERT_EQ(stat(out_path, &st), 0);
  ASSERT_GT(st.st_size, 0);
}

// Test that pass_util errors are properly propagated
TEST_F(PKeyUtlTest, PassinErrorHandling) {
  args_list_t args = {"-sign",   "-inkey",         protected_key_path,
                      "-passin", "invalid:format", "-in",
                      in_path,   "-out",           out_path};
  int result = pkeyutlTool(args);
  ASSERT_EQ(kToolExitFailure, result);

  args_list_t args2 = {"-sign",
                       "-inkey",
                       protected_key_path,
                       "-passin",
                       "pass:wrongpassword",
                       "-in",
                       in_path,
                       "-out",
                       out_path};
  int result2 = pkeyutlTool(args2);
  ASSERT_EQ(kToolExitFailure, result2);
}

// Test that unprotected key works without passin
TEST_F(PKeyUtlTest, NoPassinRequired) {
  args_list_t args = {"-sign", "-inkey", key_path, "-in",
                      in_path, "-out",   out_path};
  int result = pkeyutlTool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Verify the signature file was created and has content
  struct stat st;
  ASSERT_EQ(stat(out_path, &st), 0);
  ASSERT_GT(st.st_size, 0);
}

// Test basic signing operation
TEST_F(PKeyUtlTest, StdoutOutput) {
  args_list_t args = {"-sign", "-inkey", key_path, "-in", in_path};
  int result = pkeyutlTool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test signing with pkeyopt
TEST_F(PKeyUtlTest, Pkeyopt) {
  // Generate a hashed input
  char hashed_in_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(hashed_in_path), 0u);

  // Create a hash-sized input (32 bytes for SHA-256)
  std::ofstream hashed_in_file(hashed_in_path, std::ios::binary);
  std::string hash_data(32, 'A');  // Exactly 32 bytes
  hashed_in_file << hash_data;
  hashed_in_file.close();

  // Test sign with pkeyopt
  args_list_t args = {"-sign",
                      "-inkey",
                      key_path,
                      "-in",
                      hashed_in_path,
                      "-pkeyopt",
                      "digest:SHA256",
                      "-pkeyopt",
                      "rsa_padding_mode:pss",
                      "-pkeyopt",
                      "rsa_pss_saltlen:-1",
                      "-out",
                      sig_path};
  int result = pkeyutlTool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Verify the signature file was created and has content
  struct stat st;
  ASSERT_EQ(stat(sig_path, &st), 0);
  ASSERT_GT(st.st_size, 0);

  // Test verify with pkeyopt
  args = {"-verify",  "-pubin",
          "-inkey",   pubkey_path,
          "-in",      hashed_in_path,
          "-sigfile", sig_path,
          "-pkeyopt", "digest:SHA256",
          "-pkeyopt", "rsa_padding_mode:pss",
          "-pkeyopt", "rsa_pss_saltlen:-1",
          "-out",     out_path};
  result = pkeyutlTool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Check that the output contains "Signature Verified Successfully"
  std::string output = ReadFileToString(out_path);
  ASSERT_NE(output.find("Signature Verified Successfully"), std::string::npos);
  RemoveFile(hashed_in_path);
}

TEST_F(PKeyUtlTest, OperationFlagPrecedence) {
  struct {
    const char *name;
    args_list_t args;
    bool resolves_to_verify;
  } cases[] = {
      {"NoFlagDefaultsToSign",
       {"-inkey", key_path, "-in", in_path, "-out", sig_path},
       false},
      {"SignThenVerifyResolvesToVerify",
       {"-sign", "-verify", "-pubin", "-inkey", pubkey_path, "-in", in_path,
        "-sigfile", sig_path, "-out", out_path},
       true},
      {"VerifyThenSignResolvesToSign",
       {"-verify", "-sign", "-inkey", key_path, "-in", in_path, "-out",
        sig_path},
       false},
  };

  for (const auto &c : cases) {
    SCOPED_TRACE(c.name);
    if (c.resolves_to_verify) {
      ASSERT_NO_FATAL_FAILURE(SignExpectSuccess());
      RemoveFile(out_path);
    } else {
      RemoveFile(sig_path);
    }
    ASSERT_EQ(kToolExitSuccess, pkeyutlTool(c.args));
    if (c.resolves_to_verify) {
      EXPECT_NE(
          ReadFileToString(out_path).find("Signature Verified Successfully"),
          std::string::npos);
    } else {
      ASSERT_NO_FATAL_FAILURE(
          VerifyExpectSuccess({"-pubin", "-inkey", pubkey_path}));
    }
  }
}

// -decrypt -encrypt resolves to -encrypt, so -pubin is accepted.
TEST_F(PKeyUtlTest, LastOperationWinsToEncrypt) {
  args_list_t args = {"-decrypt", "-encrypt", "-pubin", "-inkey", pubkey_path,
                      "-in",      in_path,    "-out",   out_path};
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(args));
  EXPECT_NE(ReadFileToString(in_path), ReadFileToString(out_path));

  char decrypted_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(decrypted_path), 0u);
  args_list_t decrypt_args = {"-decrypt", "-inkey", key_path,      "-in",
                              out_path,   "-out",   decrypted_path};
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(decrypt_args));
  EXPECT_EQ(ReadFileToString(in_path), ReadFileToString(decrypted_path));
  RemoveFile(decrypted_path);
}

TEST_F(PKeyUtlTest, VerifyKeyTypes) {
  ASSERT_NO_FATAL_FAILURE(SignExpectSuccess());

  struct {
    const char *name;
    args_list_t key_args;
  } cases[] = {
      {"PrivateKey", {"-inkey", key_path}},
      {"EncryptedPrivateKeyWithPassin",
       {"-inkey", protected_key_path, "-passin", "pass:testpassword"}},
      {"PublicKeyWithPubin", {"-pubin", "-inkey", pubkey_path}},
  };

  for (const auto &c : cases) {
    SCOPED_TRACE(c.name);
    ASSERT_NO_FATAL_FAILURE(VerifyExpectSuccess(c.key_args));
  }
}

TEST_F(PKeyUtlTest, PassinArgumentLastWins) {
  args_list_t args = {"-sign",
                      "-inkey",
                      protected_key_path,
                      "-passin",
                      "pass:wrongpassword",
                      "-passin",
                      "pass:testpassword",
                      "-in",
                      in_path,
                      "-out",
                      out_path};
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(args));

  struct stat st;
  ASSERT_EQ(stat(out_path, &st), 0);
  ASSERT_GT(st.st_size, 0);
}

// --------------- PKeyUtl Pubin Rejection Tests ---------------------------

// Use a valid public key so a key-load failure cannot mask the rejection.
TEST_F(PKeyUtlTest, PubinRejectedForPrivateOperations) {
  const char *operations[] = {"-sign", "-decrypt"};
  for (const char *operation : operations) {
    SCOPED_TRACE(operation);
    args_list_t args = {operation, "-pubin", "-inkey", pubkey_path,
                        "-in",     in_path,  "-out",   out_path};
    testing::internal::CaptureStderr();
    const int result = pkeyutlTool(args);
    const std::string errors = testing::internal::GetCapturedStderr();
    EXPECT_EQ(kToolExitFailure, result);
    EXPECT_NE(std::string::npos,
              errors.find("A private key is needed for this operation"));
  }
}

// --------------- PKeyUtl Scalar Argument Last-Wins Tests -----------------

TEST_F(PKeyUtlTest, ScalarArgumentsLastWin) {
  char wrong_in_path[PATH_MAX];
  char wrong_key_path[PATH_MAX];
  char first_out_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(wrong_in_path), 0u);
  ASSERT_GT(createTempFILEpath(wrong_key_path), 0u);
  ASSERT_GT(createTempFILEpath(first_out_path), 0u);
  RemoveFile(first_out_path);  // The first -out must never be created.

  {
    ScopedFILE wrong_in_file(fopen(wrong_in_path, "wb"));
    ASSERT_TRUE(wrong_in_file);
    const char *wrong_data = "This is not the data that gets signed";
    ASSERT_EQ(fwrite(wrong_data, 1, strlen(wrong_data), wrong_in_file.get()),
              strlen(wrong_data));
  }
  bssl::UniquePtr<EVP_PKEY> wrong_pkey(CreateTestKey(2048));
  ASSERT_TRUE(wrong_pkey);
  {
    ScopedFILE wrong_key_file(fopen(wrong_key_path, "wb"));
    ASSERT_TRUE(wrong_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(wrong_key_file.get(), wrong_pkey.get(),
                                     nullptr, nullptr, 0, nullptr, nullptr));
  }


  args_list_t args = {"-sign",  "-inkey", wrong_key_path, "-inkey",
                      key_path, "-in",    wrong_in_path,  "-in",
                      in_path,  "-out",   first_out_path, "-out",
                      sig_path};
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(args));

  struct stat first_out_st;
  EXPECT_NE(0, stat(first_out_path, &first_out_st));

  // The first -sigfile does not exist.
  args_list_t verify_args = {"-verify",  "-pubin", "-inkey",   pubkey_path,
                             "-in",      in_path,  "-sigfile", first_out_path,
                             "-sigfile", sig_path, "-out",     out_path};
  ASSERT_EQ(kToolExitSuccess, pkeyutlTool(verify_args));
  EXPECT_NE(ReadFileToString(out_path).find("Signature Verified Successfully"),
            std::string::npos);

  RemoveFile(wrong_in_path);
  RemoveFile(wrong_key_path);
}

#if !defined(OPENSSL_WINDOWS)
namespace {

// Restore stdout and SIGPIPE even if an assertion exits the test early.
class BrokenStdoutPipeGuard {
 public:
  bool Init() {
    int pipefd[2];
    if (pipe(pipefd) != 0) {
      return false;
    }
    close(pipefd[0]);  // No reader: writes/flushes fail with EPIPE.
    ScopedFD write_end(pipefd[1]);
    fflush(stdout);
    old_stdout_ = ScopedFD(dup(STDOUT_FILENO));
    if (!old_stdout_) {
      return false;
    }
    old_sigpipe_ = signal(SIGPIPE, SIG_IGN);
    return old_sigpipe_ != SIG_ERR &&
           dup2(write_end.get(), STDOUT_FILENO) == STDOUT_FILENO;
  }

  ~BrokenStdoutPipeGuard() {
    if (old_stdout_) {
      dup2(old_stdout_.get(), STDOUT_FILENO);
    }
    if (old_sigpipe_ != SIG_ERR) {
      signal(SIGPIPE, old_sigpipe_);
    }
    clearerr(stdout);
  }

 private:
  ScopedFD old_stdout_;
  void (*old_sigpipe_)(int) = SIG_ERR;
};

}  // namespace

TEST_F(PKeyUtlTest, OutputWriteFailureIsReported) {
  ASSERT_NO_FATAL_FAILURE(SignExpectSuccess());
  const args_list_t cases[] = {{"-sign", "-inkey", key_path, "-in", in_path},
                               {"-verify", "-pubin", "-inkey", pubkey_path,
                                "-in", in_path, "-sigfile", sig_path}};
  for (const auto &args : cases) {
    SCOPED_TRACE(args.front());
    BrokenStdoutPipeGuard guard;
    ASSERT_TRUE(guard.Init());
    EXPECT_EQ(kToolExitFailure, pkeyutlTool(args));
  }
}
#endif  // !OPENSSL_WINDOWS

// ---------------- PKeyUtl Option Usage Error Tests ----------------------

class PKeyUtlOptionUsageErrorsTest : public PKeyUtlTest {
 protected:
  void TestOptionUsageErrors(const std::vector<std::string> &args) {
    args_list_t c_args;
    for (const auto &arg : args) {
      c_args.push_back(arg.c_str());
    }
    int result = pkeyutlTool(c_args);
    ASSERT_EQ(kToolExitFailure, result);
  }
};

// Test invalid option combinations
TEST_F(PKeyUtlOptionUsageErrorsTest, InvalidOptionCombinations) {
  std::vector<std::vector<std::string>> testparams = {
      // Missing inkey
      {"-sign", "-in", in_path},
      // Verify without sigfile
      {"-verify", "-inkey", key_path, "-in", in_path},
      // -sign -verify resolves to -verify, which needs -sigfile
      {"-sign", "-verify", "-inkey", key_path, "-in", in_path},
      // -verify -sign resolves to -sign, which rejects -sigfile
      {"-verify", "-sign", "-inkey", key_path, "-in", in_path, "-sigfile",
       sig_path},
      // Sigfile with sign operation
      {"-sign", "-inkey", key_path, "-in", in_path, "-sigfile", sig_path},
      // Wrong use of pkeyopt
      {"-sign", "-inkey", key_path, "-pkeyopt", "abc:xyz", "-in", in_path},
      // -pubin with -sign or -decrypt (including via last-wins)
      {"-encrypt", "-decrypt", "-pubin", "-inkey", pubkey_path, "-in", in_path},
      {"-decrypt", "-pubin", "-inkey", pubkey_path, "-in", in_path},
      {"-sign", "-pubin", "-inkey", pubkey_path, "-in", in_path},
  };

  for (const auto &args : testparams) {
    TestOptionUsageErrors(args);
  }
}

// ---------------- PKeyUtl OpenSSL Comparison Tests ----------------------

// Comparison tests cannot run without set up of environment variables:
// AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH.

class PKeyUtlComparisonTest : public ::testing::Test {
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
    ASSERT_GT(createTempFILEpath(sig_path_tool), 0u);
    ASSERT_GT(createTempFILEpath(sig_path_openssl), 0u);
    ASSERT_GT(createTempFILEpath(key_path), 0u);
    ASSERT_GT(createTempFILEpath(pubkey_path), 0u);

    // Create and save a private key
    pkey.reset(CreateTestKey(2048));
    ASSERT_TRUE(pkey);

    ScopedFILE key_file(fopen(key_path, "wb"));
    ASSERT_TRUE(key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(key_file.get(), pkey.get(), nullptr,
                                     nullptr, 0, nullptr, nullptr));

    // Create a public key file
    ScopedFILE pubkey_file(fopen(pubkey_path, "wb"));
    ASSERT_TRUE(pubkey_file);
    ASSERT_TRUE(PEM_write_PUBKEY(pubkey_file.get(), pkey.get()));

    // Create a test input file with some data
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    const char *test_data = "Test data";  // Shorter for RSA signing
    ASSERT_EQ(fwrite(test_data, 1, strlen(test_data), in_file.get()),
              strlen(test_data));
  }

  void TearDown() override {
    if (tool_executable_path != nullptr && openssl_executable_path != nullptr) {
      RemoveFile(in_path);
      RemoveFile(out_path_tool);
      RemoveFile(out_path_openssl);
      RemoveFile(sig_path_tool);
      RemoveFile(sig_path_openssl);
      RemoveFile(key_path);
      RemoveFile(pubkey_path);
    }
  }

  char in_path[PATH_MAX];
  char out_path_tool[PATH_MAX];
  char out_path_openssl[PATH_MAX];
  char sig_path_tool[PATH_MAX];
  char sig_path_openssl[PATH_MAX];
  char key_path[PATH_MAX];
  char pubkey_path[PATH_MAX];
  bssl::UniquePtr<EVP_PKEY> pkey;
  const char *tool_executable_path;
  const char *openssl_executable_path;
  std::string tool_output_str;
  std::string openssl_output_str;
};

// Test signing operation against OpenSSL
TEST_F(PKeyUtlComparisonTest, Sign) {
  std::string tool_command = ShellEscape(tool_executable_path) +
                             " pkeyutl -sign -inkey " + ShellEscape(key_path) +
                             " -in " + ShellEscape(in_path) + " -out " +
                             ShellEscape(sig_path_tool);
  std::string openssl_command = ShellEscape(openssl_executable_path) +
                                " pkeyutl -sign -inkey " +
                                ShellEscape(key_path) + " -in " +
                                ShellEscape(in_path) + " -out " +
                                ShellEscape(sig_path_openssl);

  int tool_result = system(tool_command.c_str());
  ASSERT_EQ(tool_result, 0) << "AWS-LC tool command failed: " << tool_command;

  int openssl_result = system(openssl_command.c_str());
  ASSERT_EQ(openssl_result, 0) << "OpenSSL command failed: " << openssl_command;

  // Verify both signatures with the public key
  std::string tool_verify_cmd = ShellEscape(tool_executable_path) +
                                " pkeyutl -verify -pubin -inkey " +
                                ShellEscape(pubkey_path) + " -in " +
                                ShellEscape(in_path) + " -sigfile " +
                                ShellEscape(sig_path_tool) + " > " +
                                ShellEscape(out_path_tool);
  std::string openssl_verify_cmd =
      ShellEscape(openssl_executable_path) + " pkeyutl -verify -pubin -inkey " +
      ShellEscape(pubkey_path) + " -in " + ShellEscape(in_path) +
      " -sigfile " + ShellEscape(sig_path_openssl) + " > " +
      ShellEscape(out_path_openssl);

  ASSERT_EQ(system(tool_verify_cmd.c_str()), 0);
  ASSERT_EQ(system(openssl_verify_cmd.c_str()), 0);

  // Read verification results
  std::ifstream tool_output(out_path_tool);
  tool_output_str = std::string((std::istreambuf_iterator<char>(tool_output)),
                                std::istreambuf_iterator<char>());
  std::ifstream openssl_output(out_path_openssl);
  openssl_output_str =
      std::string((std::istreambuf_iterator<char>(openssl_output)),
                  std::istreambuf_iterator<char>());

  // Both should verify successfully
  ASSERT_NE(tool_output_str.find("Signature Verified Successfully"),
            std::string::npos);
  ASSERT_NE(openssl_output_str.find("Signature Verified Successfully"),
            std::string::npos);

  // Cross-verification testing:
  // 1. AWS-LC signs → OpenSSL verifies
  std::string cross_verify_1 = ShellEscape(openssl_executable_path) +
                               " pkeyutl -verify -pubin -inkey " +
                               ShellEscape(pubkey_path) + " -in " +
                               ShellEscape(in_path) + " -sigfile " +
                               ShellEscape(sig_path_tool) + " > " +
                               ShellEscape(out_path_tool);
  ASSERT_EQ(system(cross_verify_1.c_str()), 0)
      << "OpenSSL failed to verify AWS-LC signature";

  // 2. OpenSSL signs → AWS-LC verifies
  std::string cross_verify_2 = ShellEscape(tool_executable_path) +
                               " pkeyutl -verify -pubin -inkey " +
                               ShellEscape(pubkey_path) + " -in " +
                               ShellEscape(in_path) + " -sigfile " +
                               ShellEscape(sig_path_openssl) + " > " +
                               ShellEscape(out_path_openssl);
  ASSERT_EQ(system(cross_verify_2.c_str()), 0)
      << "AWS-LC failed to verify OpenSSL signature";

  // Read cross-verification results
  std::ifstream cross_1_output(out_path_tool);
  std::string cross_1_str =
      std::string((std::istreambuf_iterator<char>(cross_1_output)),
                  std::istreambuf_iterator<char>());
  std::ifstream cross_2_output(out_path_openssl);
  std::string cross_2_str =
      std::string((std::istreambuf_iterator<char>(cross_2_output)),
                  std::istreambuf_iterator<char>());

  ASSERT_NE(cross_1_str.find("Signature Verified Successfully"),
            std::string::npos)
      << "OpenSSL should successfully verify AWS-LC signature";
  ASSERT_NE(cross_2_str.find("Signature Verified Successfully"),
            std::string::npos)
      << "AWS-LC should successfully verify OpenSSL signature";
}

// Test pkeyopt functionality against OpenSSL
TEST_F(PKeyUtlComparisonTest, Pkeyopt) {
  char hashed_in_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(hashed_in_path), 0u);

  std::string hash_command = ShellEscape(openssl_executable_path) +
                             " dgst -sha256 -binary " + ShellEscape(in_path) +
                             " > " + ShellEscape(hashed_in_path);

  int result = system(hash_command.c_str());
  ASSERT_EQ(result, 0) << "Input command failed: " << hash_command;

  // Test signing with pkeyopt
  std::string tool_command =
      ShellEscape(tool_executable_path) + " pkeyutl -sign -inkey " +
      ShellEscape(key_path) + " -in " + ShellEscape(hashed_in_path) +
      " -pkeyopt digest:SHA256 -pkeyopt rsa_padding_mode:pss"
      " -pkeyopt rsa_pss_saltlen:0 -out " +
      ShellEscape(sig_path_tool);
  std::string openssl_command =
      ShellEscape(openssl_executable_path) + " pkeyutl -sign -inkey " +
      ShellEscape(key_path) + " -in " + ShellEscape(hashed_in_path) +
      " -pkeyopt digest:SHA256   -pkeyopt rsa_padding_mode:pss"
      " -pkeyopt rsa_pss_saltlen:0 -out " +
      ShellEscape(sig_path_openssl);


  std::cout << "AWS-LC command: " << tool_command << std::endl;
  std::cout << "OpenSSL command: " << openssl_command << std::endl;

  int tool_result = system(tool_command.c_str());
  ASSERT_EQ(tool_result, 0) << "AWS-LC tool command failed: " << tool_command;

  int openssl_result = system(openssl_command.c_str());
  ASSERT_EQ(openssl_result, 0) << "OpenSSL command failed: " << openssl_command;

  // Test verification with pkeyopt
  std::string tool_verify_cmd =
      ShellEscape(tool_executable_path) + " pkeyutl -verify -pubin -inkey " +
      ShellEscape(pubkey_path) + " -in " + ShellEscape(hashed_in_path) +
      " -sigfile " + ShellEscape(sig_path_tool) +
      " -pkeyopt digest:SHA256 -pkeyopt rsa_padding_mode:pss"
      " -pkeyopt rsa_pss_saltlen:0 > " +
      ShellEscape(out_path_tool);
  std::string openssl_verify_cmd =
      ShellEscape(openssl_executable_path) + " pkeyutl -verify -pubin -inkey " +
      ShellEscape(pubkey_path) + " -in " + ShellEscape(hashed_in_path) +
      " -sigfile " + ShellEscape(sig_path_openssl) +
      " -pkeyopt digest:SHA256 -pkeyopt rsa_padding_mode:pss"
      " -pkeyopt rsa_pss_saltlen:0 > " +
      ShellEscape(out_path_openssl);

  ASSERT_EQ(system(tool_verify_cmd.c_str()), 0);
  ASSERT_EQ(system(openssl_verify_cmd.c_str()), 0);

  // Read verification results
  std::ifstream tool_output(out_path_tool);
  tool_output_str = std::string((std::istreambuf_iterator<char>(tool_output)),
                                std::istreambuf_iterator<char>());
  std::ifstream openssl_output(out_path_openssl);
  openssl_output_str =
      std::string((std::istreambuf_iterator<char>(openssl_output)),
                  std::istreambuf_iterator<char>());

  // Both should verify successfully
  ASSERT_NE(tool_output_str.find("Signature Verified Successfully"),
            std::string::npos);
  ASSERT_NE(openssl_output_str.find("Signature Verified Successfully"),
            std::string::npos);

  RemoveFile(hashed_in_path);
}

// Verify that pkeyutl -verify's exit status matches OpenSSL: 0 on a good
// signature and nonzero when the signature does not match the input.
TEST_F(PKeyUtlComparisonTest, VerifyExitCode) {
  std::string sign_command = std::string(tool_executable_path) +
                             " pkeyutl -sign -inkey " + key_path + " -in " +
                             in_path + " -out " + sig_path_tool;
  ASSERT_EQ(0, ExecuteCommandExitCode(sign_command));

  // Good signature: both exit 0.
  std::string tool_command = std::string(tool_executable_path) +
                             " pkeyutl -verify -pubin -inkey " + pubkey_path +
                             " -in " + in_path + " -sigfile " + sig_path_tool +
                             " > " + out_path_tool + " 2>&1";
  std::string openssl_command =
      std::string(openssl_executable_path) + " pkeyutl -verify -pubin -inkey " +
      pubkey_path + " -in " + in_path + " -sigfile " + sig_path_tool + " > " +
      out_path_openssl + " 2>&1";
  int tool_exit = ExecuteCommandExitCode(tool_command);
  int openssl_exit = ExecuteCommandExitCode(openssl_command);
  EXPECT_EQ(0, tool_exit);
  EXPECT_EQ(openssl_exit, tool_exit);

  // Bad signature: verify the signature against different input data.
  char other_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(other_path), 0u);
  {
    ScopedFILE other_file(fopen(other_path, "wb"));
    ASSERT_TRUE(other_file);
    const char *tampered = "Other data";
    ASSERT_EQ(fwrite(tampered, 1, strlen(tampered), other_file.get()),
              strlen(tampered));
  }

  tool_command = std::string(tool_executable_path) +
                 " pkeyutl -verify -pubin -inkey " + pubkey_path + " -in " +
                 other_path + " -sigfile " + sig_path_tool + " > " +
                 out_path_tool + " 2>&1";
  openssl_command = std::string(openssl_executable_path) +
                    " pkeyutl -verify -pubin -inkey " + pubkey_path + " -in " +
                    other_path + " -sigfile " + sig_path_tool + " > " +
                    out_path_openssl + " 2>&1";
  tool_exit = ExecuteCommandExitCode(tool_command);
  openssl_exit = ExecuteCommandExitCode(openssl_command);
  EXPECT_NE(0, tool_exit);
  EXPECT_EQ(openssl_exit, tool_exit);

  RemoveFile(other_path);
}

// "-" selects stdin for -in and stdout for -out, as in OpenSSL.
TEST_F(PKeyUtlComparisonTest, DashMeansStdio) {
  std::string openssl_encrypt =
      ShellEscape(openssl_executable_path) +
      " pkeyutl -encrypt -pubin -inkey " + ShellEscape(pubkey_path) + " -in " +
      ShellEscape(in_path) + " -out " + ShellEscape(sig_path_openssl);
  ASSERT_EQ(0, ExecuteCommandExitCode(openssl_encrypt));

  const std::string args = " pkeyutl -decrypt -inkey " + ShellEscape(key_path) +
                           " -in - -out - < " + ShellEscape(sig_path_openssl);
  RunCommandsAndCompareOutput(ShellEscape(tool_executable_path) + args + " > " +
                                  ShellEscape(out_path_tool),
                              ShellEscape(openssl_executable_path) + args +
                                  " > " + ShellEscape(out_path_openssl),
                              out_path_tool, out_path_openssl, tool_output_str,
                              openssl_output_str);
  EXPECT_EQ(ReadFileToString(in_path), tool_output_str);
  EXPECT_EQ(tool_output_str, openssl_output_str);
}

TEST_F(PKeyUtlComparisonTest, EncryptDecryptInteroperability) {
  const char *pkey_options[] = {
      "",
      " -pkeyopt rsa_padding_mode:oaep -pkeyopt rsa_oaep_md:sha256"
      " -pkeyopt rsa_mgf1_md:sha256",
  };

  for (const char *options : pkey_options) {
    SCOPED_TRACE(options[0] == '\0' ? "PKCS1" : "OAEP-SHA256");

    std::string tool_encrypt =
        ShellEscape(tool_executable_path) + " pkeyutl -encrypt -pubin -inkey " +
        ShellEscape(pubkey_path) + " -in " + ShellEscape(in_path) + options +
        " -out " + ShellEscape(out_path_tool);
    ASSERT_EQ(0, ExecuteCommandExitCode(tool_encrypt));

    std::string openssl_decrypt =
        ShellEscape(openssl_executable_path) + " pkeyutl -decrypt -inkey " +
        ShellEscape(key_path) + " -in " + ShellEscape(out_path_tool) + options +
        " -out " + ShellEscape(sig_path_openssl);
    ASSERT_EQ(0, ExecuteCommandExitCode(openssl_decrypt));
    EXPECT_EQ(ReadFileToString(in_path), ReadFileToString(sig_path_openssl));

    std::string openssl_encrypt = ShellEscape(openssl_executable_path) +
                                  " pkeyutl -encrypt -pubin -inkey " +
                                  ShellEscape(pubkey_path) + " -in " +
                                  ShellEscape(in_path) + options + " -out " +
                                  ShellEscape(out_path_openssl);
    ASSERT_EQ(0, ExecuteCommandExitCode(openssl_encrypt));

    std::string tool_decrypt =
        ShellEscape(tool_executable_path) + " pkeyutl -decrypt -inkey " +
        ShellEscape(key_path) + " -in " + ShellEscape(out_path_openssl) +
        options + " -out " + ShellEscape(sig_path_tool);
    ASSERT_EQ(0, ExecuteCommandExitCode(tool_decrypt));
    EXPECT_EQ(ReadFileToString(in_path), ReadFileToString(sig_path_tool));
  }
}

// ------------- PKeyUtl Operation Resolution Comparison Tests -------------

// With no operation flag at all, both tools default to -sign.
TEST_F(PKeyUtlComparisonTest, DefaultOperationIsSign) {
  const char *executables[] = {tool_executable_path, openssl_executable_path};
  const char *sig_paths[] = {sig_path_tool, sig_path_openssl};
  const char *out_paths[] = {out_path_tool, out_path_openssl};

  for (int i = 0; i < 2; i++) {
    std::string sign_command = ShellEscape(executables[i]) +
                               " pkeyutl -inkey " + ShellEscape(key_path) +
                               " -in " + ShellEscape(in_path) + " -out " +
                               ShellEscape(sig_paths[i]);
    ASSERT_EQ(0, ExecuteCommandExitCode(sign_command));

    std::string verify_command =
        ShellEscape(executables[i]) + " pkeyutl -verify -pubin -inkey " +
        ShellEscape(pubkey_path) + " -in " + ShellEscape(in_path) +
        " -sigfile " + ShellEscape(sig_paths[i]) + " > " +
        ShellEscape(out_paths[i]);
    ASSERT_EQ(0, ExecuteCommandExitCode(verify_command));

    EXPECT_NE(
        ReadFileToString(out_paths[i]).find("Signature Verified Successfully"),
        std::string::npos);
  }
}

TEST_F(PKeyUtlComparisonTest, LastOperationFlagWins) {
  // -sign -verify resolves to -verify.
  std::string sign_command = ShellEscape(tool_executable_path) +
                             " pkeyutl -sign -inkey " + ShellEscape(key_path) +
                             " -in " + ShellEscape(in_path) + " -out " +
                             ShellEscape(sig_path_tool);
  ASSERT_EQ(0, ExecuteCommandExitCode(sign_command));

  const char *executables[] = {tool_executable_path, openssl_executable_path};
  const char *out_paths[] = {out_path_tool, out_path_openssl};
  for (int i = 0; i < 2; i++) {
    std::string verify_command =
        ShellEscape(executables[i]) + " pkeyutl -sign -verify -pubin -inkey " +
        ShellEscape(pubkey_path) + " -in " + ShellEscape(in_path) +
        " -sigfile " + ShellEscape(sig_path_tool) + " -out " +
        ShellEscape(out_paths[i]);
    ASSERT_EQ(0, ExecuteCommandExitCode(verify_command));
    EXPECT_NE(
        ReadFileToString(out_paths[i]).find("Signature Verified Successfully"),
        std::string::npos);
  }

  // -verify -sign resolves to -sign, which rejects -sigfile.
  for (const char *executable : executables) {
    std::string rejected_command =
        ShellEscape(executable) + " pkeyutl -verify -sign -inkey " +
        ShellEscape(key_path) + " -in " + ShellEscape(in_path) + " -sigfile " +
        ShellEscape(sig_path_tool);
    EXPECT_NE(0, ExecuteCommandExitCode(rejected_command));
  }
}

// -verify accepts an encrypted private key via -passin.
TEST_F(PKeyUtlComparisonTest, VerifyWithEncryptedPrivateKeyPassin) {
  char protected_key_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(protected_key_path), 0u);
  {
    ScopedFILE protected_key_file(fopen(protected_key_path, "wb"));
    ASSERT_TRUE(protected_key_file);
    ASSERT_TRUE(PEM_write_PrivateKey(
        protected_key_file.get(), pkey.get(), EVP_aes_256_cbc(),
        (unsigned char *)"testpassword", 12, nullptr, nullptr));
  }

  std::string sign_command =
      ShellEscape(tool_executable_path) + " pkeyutl -sign -inkey " +
      ShellEscape(protected_key_path) + " -passin pass:testpassword -in " +
      ShellEscape(in_path) + " -out " + ShellEscape(sig_path_tool);
  ASSERT_EQ(0, ExecuteCommandExitCode(sign_command));

  const char *executables[] = {tool_executable_path, openssl_executable_path};
  const char *out_paths[] = {out_path_tool, out_path_openssl};
  for (int i = 0; i < 2; i++) {
    std::string verify_command =
        ShellEscape(executables[i]) + " pkeyutl -verify -inkey " +
        ShellEscape(protected_key_path) + " -passin pass:testpassword -in " +
        ShellEscape(in_path) + " -sigfile " + ShellEscape(sig_path_tool) +
        " > " + ShellEscape(out_paths[i]);
    ASSERT_EQ(0, ExecuteCommandExitCode(verify_command));
    EXPECT_NE(
        ReadFileToString(out_paths[i]).find("Signature Verified Successfully"),
        std::string::npos);
  }

  RemoveFile(protected_key_path);
}

// -pubin cannot be combined with -sign or -decrypt in either tool.
TEST_F(PKeyUtlComparisonTest, PubinRejectedForPrivateOps) {
  const char *executables[] = {tool_executable_path, openssl_executable_path};
  const char *sig_paths[] = {sig_path_tool, sig_path_openssl};
  const char *operations[] = {"-sign", "-decrypt"};

  for (int i = 0; i < 2; i++) {
    for (const char *operation : operations) {
      std::string command =
          ShellEscape(executables[i]) + " pkeyutl " + operation +
          " -pubin -inkey " + ShellEscape(pubkey_path) + " -in " +
          ShellEscape(in_path) + " -out " + ShellEscape(sig_paths[i]);
      EXPECT_NE(0, ExecuteCommandExitCode(command));
    }
  }
}
