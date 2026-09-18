// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/ec.h>
#include <openssl/pem.h>
#include <fstream>
#include <iterator>
#include <ostream>

#if defined(OPENSSL_WINDOWS)
#include <direct.h>
#else
#include <unistd.h>
#endif
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

// Test certificate without -CAfile. The default trust store does not contain
// the self-signed test certificate, so this is a verification failure (2)
// rather than an option error (1).
TEST_F(VerifyTest, SelfSignedCertWithoutCAfile) {
  args_list_t args = {in_path};
  int result = VerifyTool(args);
  ASSERT_EQ(2, result);
}

// Test certificate with -untrusted
TEST_F(VerifyTest, SelfSignedCertWithUntrustedChain) {
  args_list_t args = {"-untrusted", chain_path, in_path};
  int result = VerifyTool(args);
  ASSERT_EQ(2, result);
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
  const char *garbage = "not a certificate\n";
  ASSERT_EQ(fwrite(garbage, 1, strlen(garbage), in_file.get()),
            strlen(garbage));
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

// TempCertPath is a unique temp file path, removed when it goes out of scope.
struct TempCertPath {
  ~TempCertPath() { RemoveFile(path); }
  bool Init() { return createTempFILEpath(path) > 0; }
  char path[PATH_MAX] = {};
};

// IssueTestCert extends MakeTestCert (crypto/test/test_util.h) with a
// validity window around the current time, then signs with |issuer_key|
// (pass |key| itself to self-sign a root).
static bssl::UniquePtr<X509> IssueTestCert(const char *issuer,
                                           const char *subject, EVP_PKEY *key,
                                           EVP_PKEY *issuer_key, bool is_ca) {
  bssl::UniquePtr<X509> cert = MakeTestCert(issuer, subject, key, is_ca);
  if (!cert || !X509_gmtime_adj(X509_getm_notBefore(cert.get()), 0) ||
      !X509_gmtime_adj(X509_getm_notAfter(cert.get()), 60 * 60 * 24 * 30) ||
      X509_sign(cert.get(), issuer_key, EVP_sha256()) <= 0) {
    return nullptr;
  }
  return cert;
}

static bool WriteCertPEM(const char *path, X509 *cert) {
  ScopedFILE f(fopen(path, "wb"));
  return f && PEM_write_X509(f.get(), cert);
}

// Two leaves issued by the same intermediate must both verify from a single
// VerifyTool call given a root-only -CAfile and an intermediate-only
// -untrusted; a leaf must fail to verify without the intermediate, and a
// failing input ahead of the leaves must not short-circuit the loop.
TEST(VerifyExitCodeTest, SharedUntrustedIntermediateVerifiesBothLeaves) {
  bssl::UniquePtr<EVP_PKEY> root_key(CreateTestKey(2048));
  bssl::UniquePtr<EVP_PKEY> mid_key(CreateTestKey(2048));
  bssl::UniquePtr<EVP_PKEY> leaf1_key(CreateTestKey(2048));
  bssl::UniquePtr<EVP_PKEY> leaf2_key(CreateTestKey(2048));
  ASSERT_TRUE(root_key && mid_key && leaf1_key && leaf2_key);

  bssl::UniquePtr<X509> root =
      IssueTestCert("Root", "Root", root_key.get(), root_key.get(), true);
  bssl::UniquePtr<X509> mid =
      IssueTestCert("Root", "Mid", mid_key.get(), root_key.get(), true);
  bssl::UniquePtr<X509> leaf1 =
      IssueTestCert("Mid", "Leaf1", leaf1_key.get(), mid_key.get(), false);
  bssl::UniquePtr<X509> leaf2 =
      IssueTestCert("Mid", "Leaf2", leaf2_key.get(), mid_key.get(), false);
  ASSERT_TRUE(root && mid && leaf1 && leaf2);

  TempCertPath ca_path, untrusted_path, leaf1_path, leaf2_path;
  for (TempCertPath *file :
       {&ca_path, &untrusted_path, &leaf1_path, &leaf2_path}) {
    ASSERT_TRUE(file->Init());
  }
  ASSERT_TRUE(WriteCertPEM(ca_path.path, root.get()));
  ASSERT_TRUE(WriteCertPEM(untrusted_path.path, mid.get()));
  ASSERT_TRUE(WriteCertPEM(leaf1_path.path, leaf1.get()));
  ASSERT_TRUE(WriteCertPEM(leaf2_path.path, leaf2.get()));

  // The root alone cannot validate a leaf issued by the intermediate.
  args_list_t no_untrusted = {"-CAfile", ca_path.path, leaf1_path.path};
  EXPECT_EQ(2, VerifyTool(no_untrusted));

  // Both leaves verify against the shared intermediate in one invocation.
  args_list_t both = {"-CAfile",           ca_path.path,    "-untrusted",
                      untrusted_path.path, leaf1_path.path, leaf2_path.path};
  testing::internal::CaptureStdout();
  int result = VerifyTool(both);
  std::string out = testing::internal::GetCapturedStdout();
  const std::string expected_output =
      std::string(leaf1_path.path) + ": OK\n" + leaf2_path.path + ": OK\n";
  EXPECT_EQ(kToolExitSuccess, result);
  EXPECT_EQ(expected_output, out);

  // A failing input ahead of the leaves must not stop them being checked.
  char missing_path[PATH_MAX];
  ASSERT_GT(createTempFILEpath(missing_path), 0u);
  RemoveFile(missing_path);
  args_list_t failing_first = {
      "-CAfile",    ca_path.path,    "-untrusted",   untrusted_path.path,
      missing_path, leaf1_path.path, leaf2_path.path};
  testing::internal::CaptureStdout();
  result = VerifyTool(failing_first);
  out = testing::internal::GetCapturedStdout();
  EXPECT_EQ(2, result);
  EXPECT_EQ(expected_output, out);
}

namespace {

class VerifyTempFile {
 public:
  VerifyTempFile() = default;
  VerifyTempFile(const VerifyTempFile &) = delete;
  VerifyTempFile &operator=(const VerifyTempFile &) = delete;
  ~VerifyTempFile() { RemoveFile(path_); }

  bool Init() { return createTempFILEpath(path_) > 0; }
  std::string path() const { return path_; }
  ScopedFILE Open(const char *mode) const {
    return ScopedFILE(fopen(path_, mode));
  }

 private:
  char path_[PATH_MAX] = {};
};

class ScopedVerifyEnv {
 public:
  explicit ScopedVerifyEnv(const char *name) : name_(name) {
    const char *value = getenv(name);
    was_set_ = value != nullptr;
    if (was_set_) {
      value_ = value;
    }
  }
  ~ScopedVerifyEnv() {
    if (was_set_) {
      Set(value_);
    } else {
#if defined(OPENSSL_WINDOWS)
      _putenv_s(name_, "");
#else
      unsetenv(name_);
#endif
    }
  }
  bool Set(const std::string &value) {
#if defined(OPENSSL_WINDOWS)
    return _putenv_s(name_, value.c_str()) == 0;
#else
    return setenv(name_, value.c_str(), 1) == 0;
#endif
  }

 private:
  const char *name_;
  bool was_set_;
  std::string value_;
};

bssl::UniquePtr<EVP_PKEY> MakeVerifyKey() {
  bssl::UniquePtr<EVP_PKEY> key(EVP_PKEY_new());
  bssl::UniquePtr<EC_KEY> ec(EC_KEY_new_by_curve_name(NID_X9_62_prime256v1));
  if (!key || !ec || !EC_KEY_generate_key(ec.get()) ||
      !EVP_PKEY_set1_EC_KEY(key.get(), ec.get())) {
    return nullptr;
  }
  return key;
}

bssl::UniquePtr<X509> MakeVerifyCert(const char *issuer, const char *subject,
                                     EVP_PKEY *key, EVP_PKEY *signer, bool ca,
                                     long serial) {
  auto cert = MakeTestCert(issuer, subject, key, ca);
  bssl::UniquePtr<X509_EXTENSION> usage(X509V3_EXT_conf_nid(
      nullptr, nullptr, NID_key_usage,
      const_cast<char *>(ca ? "critical,keyCertSign,cRLSign"
                            : "critical,digitalSignature")));
  if (!cert || !usage || !X509_add_ext(cert.get(), usage.get(), -1) ||
      !ASN1_INTEGER_set(X509_get_serialNumber(cert.get()), serial) ||
      !X509_gmtime_adj(X509_getm_notBefore(cert.get()), -3600) ||
      !X509_gmtime_adj(X509_getm_notAfter(cert.get()), 86400) ||
      !X509_sign(cert.get(), signer, EVP_sha256())) {
    return nullptr;
  }
  return cert;
}

bool SetVerifyEKU(X509 *cert, const char *purpose, EVP_PKEY *signer) {
  int idx = X509_get_ext_by_NID(cert, NID_ext_key_usage, -1);
  if (idx >= 0) {
    X509_EXTENSION_free(X509_delete_ext(cert, idx));
  }
  bssl::UniquePtr<X509_EXTENSION> eku(X509V3_EXT_conf_nid(
      nullptr, nullptr, NID_ext_key_usage, const_cast<char *>(purpose)));
  return eku && X509_add_ext(cert, eku.get(), -1) &&
         X509_sign(cert, signer, EVP_sha256());
}

bool WriteVerifyCerts(const std::string &path,
                      const std::vector<X509 *> &certs) {
  ScopedFILE file(fopen(path.c_str(), "wb"));
  if (!file) {
    return false;
  }
  for (X509 *cert : certs) {
    if (!PEM_write_X509(file.get(), cert)) {
      return false;
    }
  }
  return fflush(file.get()) == 0;
}

// Read diagnostics in text mode so reference OpenSSL's CRLF on Windows is
// comparable to AWS-LC's binary-mode stdout, which uses LF.
std::string ReadVerifyOutput(const std::string &path) {
  std::ifstream file(path);
  return std::string(std::istreambuf_iterator<char>(file),
                     std::istreambuf_iterator<char>());
}

}  // namespace

class VerifyChainTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_TRUE(root_file_.Init());
    ASSERT_TRUE(leaf_file_.Init());
    ASSERT_TRUE(bundle_file_.Init());
    ASSERT_TRUE(empty_file_.Init());
    ASSERT_GT(createTempDirPath(ca_dir_), 0u);
    root_key_ = MakeVerifyKey();
    intermediate_key_ = MakeVerifyKey();
    leaf_key_ = MakeVerifyKey();
    ASSERT_TRUE(root_key_);
    ASSERT_TRUE(intermediate_key_);
    ASSERT_TRUE(leaf_key_);
    root_ = MakeVerifyCert("Verify root", "Verify root", root_key_.get(),
                           root_key_.get(), true, 1);
    intermediate_ =
        MakeVerifyCert("Verify root", "Verify intermediate",
                       intermediate_key_.get(), root_key_.get(), true, 2);
    leaf_ = MakeVerifyCert("Verify intermediate", "server.example",
                           leaf_key_.get(), intermediate_key_.get(), false, 3);
    ASSERT_TRUE(root_);
    ASSERT_TRUE(intermediate_);
    ASSERT_TRUE(leaf_);
    ASSERT_TRUE(
        SetVerifyEKU(leaf_.get(), "serverAuth", intermediate_key_.get()));
    ASSERT_TRUE(WriteVerifyCerts(root_file_.path(), {root_.get()}));
    ASSERT_TRUE(WriteInputs());
    char hash[16];
    snprintf(hash, sizeof(hash), "%08x.0", X509_subject_name_hash(root_.get()));
    hashed_root_ = std::string(ca_dir_) + "/" + hash;
    ASSERT_TRUE(WriteVerifyCerts(hashed_root_, {root_.get()}));
  }

  void TearDown() override {
    if (!hashed_root_.empty()) {
      RemoveFile(hashed_root_.c_str());
    }
    if (ca_dir_[0] != '\0') {
#if defined(OPENSSL_WINDOWS)
      _rmdir(ca_dir_);
#else
      rmdir(ca_dir_);
#endif
    }
  }

  bool WriteInputs() {
    return WriteVerifyCerts(leaf_file_.path(), {leaf_.get()}) &&
           WriteVerifyCerts(bundle_file_.path(),
                            {leaf_.get(), intermediate_.get()});
  }

  args_list_t CallerArgs() const {
    // The leaf and intermediate bundle is deliberately used twice by callers.
    return {
        "-CApath",   ca_dir_,      "-verbose",          "-purpose",
        "sslserver", "-untrusted", bundle_file_.path(), bundle_file_.path()};
  }

  char ca_dir_[PATH_MAX] = {};
  std::string hashed_root_;
  VerifyTempFile root_file_, leaf_file_, bundle_file_, empty_file_;
  bssl::UniquePtr<EVP_PKEY> root_key_, intermediate_key_, leaf_key_;
  bssl::UniquePtr<X509> root_, intermediate_, leaf_;
};

TEST_F(VerifyChainTest, CertificateValidatorInvocation) {
  EXPECT_EQ(kToolExitSuccess, VerifyTool(CallerArgs()));
}

TEST_F(VerifyChainTest, CAFileAndCAPath) {
  auto args = CallerArgs();
  args.insert(args.begin(), {"-CAfile", root_file_.path()});
  EXPECT_EQ(kToolExitSuccess, VerifyTool(args));
}

TEST_F(VerifyChainTest, PurposeIsEnforced) {
  ASSERT_TRUE(SetVerifyEKU(leaf_.get(), "clientAuth", intermediate_key_.get()));
  ASSERT_TRUE(WriteInputs());
  EXPECT_NE(kToolExitSuccess, VerifyTool(CallerArgs()));
  EXPECT_EQ(
      kToolExitSuccess,
      VerifyTool({"-CApath", ca_dir_, "-purpose", "sslclient", "-untrusted",
                  bundle_file_.path(), bundle_file_.path()}));
  EXPECT_EQ(kToolExitSuccess,
            VerifyTool({"-CApath", ca_dir_, "-purpose", "any", "-untrusted",
                        bundle_file_.path(), bundle_file_.path()}));
}

TEST_F(VerifyChainTest, ServerPurposeDoesNotAcceptClientPurpose) {
  EXPECT_NE(
      kToolExitSuccess,
      VerifyTool({"-CApath", ca_dir_, "-purpose", "sslclient", "-untrusted",
                  bundle_file_.path(), bundle_file_.path()}));
}

TEST_F(VerifyChainTest, IntermediatePurposeIsEnforced) {
  ASSERT_TRUE(SetVerifyEKU(intermediate_.get(), "clientAuth", root_key_.get()));
  ASSERT_TRUE(WriteInputs());
  EXPECT_NE(kToolExitSuccess, VerifyTool(CallerArgs()));
}

TEST_F(VerifyChainTest, UnspecifiedPurposeDoesNotCheckEKU) {
  ASSERT_TRUE(SetVerifyEKU(leaf_.get(), "clientAuth", intermediate_key_.get()));
  ASSERT_TRUE(WriteInputs());
  EXPECT_EQ(kToolExitSuccess,
            VerifyTool({"-CApath", ca_dir_, "-untrusted", bundle_file_.path(),
                        bundle_file_.path()}));
}

TEST_F(VerifyChainTest, NoEKUAllowsServerPurpose) {
  int idx = X509_get_ext_by_NID(leaf_.get(), NID_ext_key_usage, -1);
  ASSERT_GE(idx, 0);
  X509_EXTENSION_free(X509_delete_ext(leaf_.get(), idx));
  ASSERT_TRUE(X509_sign(leaf_.get(), intermediate_key_.get(), EVP_sha256()));
  ASSERT_TRUE(WriteInputs());
  EXPECT_EQ(kToolExitSuccess, VerifyTool(CallerArgs()));
}

struct VerifyTrustCase {
  const char *purpose;
  int trust_nid;
  int reject_nid;
  int expected_exit_code;
};

// Without a printer, gtest falls back to hex-dumping the raw bytes of each
// parameter, including the struct's uninitialized padding, which Valgrind
// reports as a use of uninitialised values.
static void PrintTo(const VerifyTrustCase &c, std::ostream *os) {
  *os << "{purpose=" << (c.purpose ? c.purpose : "(none)")
      << ", trust_nid=" << c.trust_nid << ", reject_nid=" << c.reject_nid
      << ", expected_exit_code=" << c.expected_exit_code << "}";
}

class VerifyTrustTest : public VerifyChainTest,
                        public ::testing::WithParamInterface<VerifyTrustCase> {
 protected:
  void SetUp() override {
    VerifyChainTest::SetUp();
    ASSERT_FALSE(HasFatalFailure());
    // Both TLS purposes pass EKU checks, isolating the root's auxiliary trust.
    ASSERT_TRUE(SetVerifyEKU(leaf_.get(), "serverAuth,clientAuth",
                             intermediate_key_.get()));
    ASSERT_TRUE(WriteInputs());
    const auto &test = GetParam();
    if (test.trust_nid != NID_undef) {
      ASSERT_TRUE(
          X509_add1_trust_object(root_.get(), OBJ_nid2obj(test.trust_nid)));
    }
    if (test.reject_nid != NID_undef) {
      ASSERT_TRUE(
          X509_add1_reject_object(root_.get(), OBJ_nid2obj(test.reject_nid)));
    }
    // Ordinary PEM_write_X509 would discard the auxiliary trust attributes.
    for (const auto &path : {root_file_.path(), hashed_root_}) {
      ScopedFILE file(fopen(path.c_str(), "wb"));
      ASSERT_TRUE(file);
      ASSERT_TRUE(PEM_write_X509_AUX(file.get(), root_.get()));
      ASSERT_EQ(0, fflush(file.get()));
    }
  }

  args_list_t VerificationArgs(const std::string &source) const {
    args_list_t args = {
        "-no-CAfile", "-no-CApath",
        source,       source == "-CAfile" ? root_file_.path() : ca_dir_,
        "-untrusted", bundle_file_.path()};
    if (GetParam().purpose != nullptr) {
      args.insert(args.end(), {"-purpose", GetParam().purpose});
    }
    args.push_back(leaf_file_.path());
    return args;
  }
};

TEST_P(VerifyTrustTest, AuxiliaryTrust) {
  for (const char *source : {"-CAfile", "-CApath"}) {
    SCOPED_TRACE(source);
    EXPECT_EQ(GetParam().expected_exit_code,
              VerifyTool(VerificationArgs(source)));
  }
}

TEST_P(VerifyTrustTest, OpenSSLComparison) {
  const char *awslc = getenv("AWSLC_TOOL_PATH");
  const char *openssl = getenv("OPENSSL_TOOL_PATH");
  if (awslc == nullptr || openssl == nullptr) {
    GTEST_SKIP() << "AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH are required";
  }
  VerifyTempFile output;
  ASSERT_TRUE(output.Init());
  for (const char *source : {"-CAfile", "-CApath"}) {
    SCOPED_TRACE(source);
    for (const char *tool : {awslc, openssl}) {
      SCOPED_TRACE(tool);
      std::string command = "\"" + std::string(tool) + "\" verify";
      for (const auto &arg : VerificationArgs(source)) {
        command += " \"" + arg + "\"";
      }
      command += " > \"" + output.path() + "\" 2>&1";
      EXPECT_EQ(GetParam().expected_exit_code, ExecuteCommandExitCode(command))
          << ReadVerifyOutput(output.path());
    }
  }
}

INSTANTIATE_TEST_SUITE_P(
    VerifyTrustAttributes, VerifyTrustTest,
    ::testing::Values(
        VerifyTrustCase{"sslserver", NID_server_auth, NID_undef, 0},
        VerifyTrustCase{"sslserver", NID_undef, NID_server_auth, 2},
        VerifyTrustCase{"sslserver", NID_client_auth, NID_undef, 2},
        VerifyTrustCase{"sslserver", NID_server_auth, NID_server_auth, 2},
        VerifyTrustCase{"sslclient", NID_client_auth, NID_undef, 0},
        VerifyTrustCase{"sslclient", NID_undef, NID_client_auth, 2},
        VerifyTrustCase{"sslclient", NID_server_auth, NID_undef, 2},
        // Any and unspecified purposes retain the default trust check, rather
        // than adopting either TLS purpose's trust settings.
        VerifyTrustCase{"any", NID_undef, NID_server_auth, 0},
        VerifyTrustCase{"any", NID_undef, NID_client_auth, 0},
        VerifyTrustCase{"any", NID_undef, NID_anyExtendedKeyUsage, 2},
        VerifyTrustCase{nullptr, NID_undef, NID_server_auth, 0},
        VerifyTrustCase{nullptr, NID_undef, NID_anyExtendedKeyUsage, 2}));

TEST_F(VerifyChainTest, InvalidArguments) {
  EXPECT_EQ(kToolExitSuccess, VerifyTool({"-help"}));
  for (const auto &args : std::vector<args_list_t>{
           {"-purpose", "not-a-purpose", leaf_file_.path()},
           {"-purpose", "", leaf_file_.path()},
           {"-purpose"},
           {"-CApath"},
           {"-CAfile"},
           {"-untrusted"},
           {"-CApath", "", leaf_file_.path()},
           {"-CAfile", "", leaf_file_.path()},
           {"-CAfile", empty_file_.path(), leaf_file_.path()},
           {"-CApath", ca_dir_, "-untrusted", "", leaf_file_.path()},
           {"-unknown"},
       }) {
    EXPECT_NE(kToolExitSuccess, VerifyTool(args));
  }
}

TEST_F(VerifyChainTest, MissingIntermediate) {
  EXPECT_NE(kToolExitSuccess, VerifyTool({"-CApath", ca_dir_, "-purpose",
                                          "sslserver", leaf_file_.path()}));
}

TEST_F(VerifyChainTest, MissingTrustAnchor) {
  ASSERT_EQ(remove(hashed_root_.c_str()), 0);
  EXPECT_NE(kToolExitSuccess, VerifyTool(CallerArgs()));
}

TEST_F(VerifyChainTest, WrongTrustAnchor) {
  auto key = MakeVerifyKey();
  ASSERT_TRUE(key);
  auto wrong_root = MakeVerifyCert("Verify root", "Verify root", key.get(),
                                   key.get(), true, 4);
  ASSERT_TRUE(wrong_root);
  ASSERT_TRUE(WriteVerifyCerts(hashed_root_, {wrong_root.get()}));
  EXPECT_NE(kToolExitSuccess, VerifyTool(CallerArgs()));
}

TEST_F(VerifyChainTest, UntrustedRootDoesNotBecomeTrusted) {
  ASSERT_EQ(remove(hashed_root_.c_str()), 0);
  ASSERT_TRUE(WriteVerifyCerts(
      bundle_file_.path(), {leaf_.get(), intermediate_.get(), root_.get()}));
  EXPECT_NE(kToolExitSuccess, VerifyTool(CallerArgs()));
}

TEST_F(VerifyChainTest, ExpiredCertificateStillFails) {
  ASSERT_TRUE(X509_gmtime_adj(X509_getm_notBefore(leaf_.get()), -7200));
  ASSERT_TRUE(X509_gmtime_adj(X509_getm_notAfter(leaf_.get()), -3600));
  ASSERT_TRUE(X509_sign(leaf_.get(), intermediate_key_.get(), EVP_sha256()));
  ASSERT_TRUE(WriteInputs());
  EXPECT_NE(kToolExitSuccess, VerifyTool(CallerArgs()));
}

TEST_F(VerifyChainTest, VerboseDoesNotChangeVerificationResult) {
  EXPECT_EQ(
      kToolExitSuccess,
      VerifyTool({"-CApath", ca_dir_, "-purpose", "sslserver", "-untrusted",
                  bundle_file_.path(), bundle_file_.path()}));
  EXPECT_EQ(kToolExitSuccess, VerifyTool(CallerArgs()));
  ASSERT_TRUE(SetVerifyEKU(leaf_.get(), "clientAuth", intermediate_key_.get()));
  ASSERT_TRUE(WriteInputs());
  EXPECT_NE(
      kToolExitSuccess,
      VerifyTool({"-CApath", ca_dir_, "-purpose", "sslserver", "-untrusted",
                  bundle_file_.path(), bundle_file_.path()}));
  EXPECT_NE(kToolExitSuccess, VerifyTool(CallerArgs()));
}

TEST_F(VerifyChainTest, MultipleInputsAndExplicitPathsWithDefaultsDisabled) {
  EXPECT_EQ(
      kToolExitSuccess,
      VerifyTool({"-no-CAfile", "-no-CApath", "-CAfile", root_file_.path(),
                  "-CApath", ca_dir_, "-untrusted", bundle_file_.path(),
                  leaf_file_.path(), bundle_file_.path()}));
  EXPECT_NE(kToolExitSuccess,
            VerifyTool({"-no-CAfile", "-no-CApath", "-CAfile",
                        root_file_.path(), "-untrusted", bundle_file_.path(),
                        leaf_file_.path(), empty_file_.path()}));
}

TEST_F(VerifyChainTest, ReportsEachInputFailureBeforeContinuing) {
  VerifyTempFile missing;
  ASSERT_TRUE(missing.Init());
  ASSERT_EQ(0, remove(missing.path().c_str()));

  for (bool verbose : {false, true}) {
    for (const std::string &next : {root_file_.path(), missing.path()}) {
      SCOPED_TRACE(verbose);
      SCOPED_TRACE(next);
      args_list_t args = {"-no-CAfile",      "-no-CApath",       "-CAfile",
                          root_file_.path(), empty_file_.path(), next};
      if (verbose) {
        args.insert(args.begin(), "-verbose");
      }
      testing::internal::CaptureStdout();
      testing::internal::CaptureStderr();
      const int result = VerifyTool(args);
      const std::string err = testing::internal::GetCapturedStderr();
      const std::string out = testing::internal::GetCapturedStdout();
      EXPECT_EQ(2, result);
      EXPECT_NE(std::string::npos, err.find("error " + empty_file_.path() +
                                            ": reading certificate failed"));
      EXPECT_NE(std::string::npos, err.find("NO_START_LINE"));
      EXPECT_EQ(0u, ERR_peek_error());
      if (next == root_file_.path()) {
        EXPECT_EQ(next + ": OK\n", out);
      } else {
        EXPECT_TRUE(out.empty());
        EXPECT_NE(std::string::npos,
                  err.find("error " + next + ": reading certificate failed"));
      }
    }
  }
}

TEST_F(VerifyChainTest, MalformedUntrustedBundle) {
  EXPECT_NE(kToolExitSuccess,
            VerifyTool({"-CApath", ca_dir_, "-untrusted", empty_file_.path(),
                        leaf_file_.path()}));
  auto file = bundle_file_.Open("ab");
  ASSERT_TRUE(file);
  ASSERT_GT(fputs("-----BEGIN CERTIFICATE-----\ninvalid\n"
                  "-----END CERTIFICATE-----\n",
                  file.get()),
            -1);
  file.reset();
  EXPECT_NE(kToolExitSuccess, VerifyTool(CallerArgs()));
}

TEST_F(VerifyChainTest, DefaultTrustSources) {
  ScopedVerifyEnv cafile("SSL_CERT_FILE"), capath("SSL_CERT_DIR");
  ASSERT_TRUE(cafile.Set(root_file_.path()));
  ASSERT_TRUE(capath.Set(ca_dir_));
  // Positional arguments without options must verify, not print usage.
  EXPECT_EQ(kToolExitSuccess, VerifyTool({root_file_.path()}));
  EXPECT_NE(kToolExitSuccess, VerifyTool({empty_file_.path()}));
  EXPECT_EQ(kToolExitSuccess,
            VerifyTool({"-no-CAfile", "-untrusted", bundle_file_.path(),
                        leaf_file_.path()}));
  EXPECT_EQ(kToolExitSuccess,
            VerifyTool({"-no-CApath", "-untrusted", bundle_file_.path(),
                        leaf_file_.path()}));
  EXPECT_NE(kToolExitSuccess,
            VerifyTool({"-no-CAfile", "-no-CApath", "-untrusted",
                        bundle_file_.path(), leaf_file_.path()}));
  // An explicit path replaces, rather than supplements, its default source.
  EXPECT_EQ(kToolExitFailure, VerifyTool({"-CAfile", empty_file_.path(),
                                          "-no-CApath", root_file_.path()}));
  EXPECT_EQ(2, VerifyTool({"-CAfile", root_file_.path(), "-no-CApath",
                           "-untrusted", bundle_file_.path(), "-purpose",
                           "sslclient", leaf_file_.path()}));
}

// As in OpenSSL, a -CApath that is not a directory is a setup error (exit 1),
// not a verification failure (exit 2), even when the default locations would
// have trusted the chain.
TEST_F(VerifyChainTest, CAPathMustBeDirectory) {
  ScopedVerifyEnv cafile("SSL_CERT_FILE"), capath("SSL_CERT_DIR");
  ASSERT_TRUE(cafile.Set(root_file_.path()));
  ASSERT_TRUE(capath.Set(ca_dir_));
  EXPECT_EQ(kToolExitFailure,
            VerifyTool({"-CApath", std::string(ca_dir_) + "/missing",
                        "-untrusted", bundle_file_.path(), leaf_file_.path()}));
  EXPECT_EQ(kToolExitFailure,
            VerifyTool({"-CApath", root_file_.path(), "-untrusted",
                        bundle_file_.path(), leaf_file_.path()}));
}

TEST_F(VerifyChainTest, EmptyDefaultLocationsDoNotOverrideExplicitTrust) {
  ScopedVerifyEnv cafile("SSL_CERT_FILE"), capath("SSL_CERT_DIR");
  ASSERT_TRUE(cafile.Set(""));
  ASSERT_TRUE(capath.Set(""));
  EXPECT_EQ(kToolExitSuccess,
            VerifyTool({"-CAfile", root_file_.path(), "-untrusted",
                        bundle_file_.path(), leaf_file_.path()}));
  EXPECT_EQ(kToolExitSuccess, VerifyTool(CallerArgs()));
}

TEST_F(VerifyChainTest, OpenSSLDefaultStoreAndStdinComparison) {
  const char *awslc = getenv("AWSLC_TOOL_PATH");
  const char *openssl = getenv("OPENSSL_TOOL_PATH");
  if (awslc == nullptr || openssl == nullptr) {
    GTEST_SKIP() << "AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH are required";
  }
  ScopedVerifyEnv cafile("SSL_CERT_FILE"), capath("SSL_CERT_DIR");
  ASSERT_TRUE(cafile.Set(root_file_.path()));
  ASSERT_TRUE(capath.Set(ca_dir_));
  VerifyTempFile output;
  ASSERT_TRUE(output.Init());
  for (const char *tool : {awslc, openssl}) {
    SCOPED_TRACE(tool);
    std::string command = "\"" + std::string(tool) + "\" verify < \"" +
                          root_file_.path() + "\" > \"" + output.path() +
                          "\" 2>&1";
    ASSERT_EQ(ExecuteCommandExitCode(command), 0);
    EXPECT_EQ(ReadVerifyOutput(output.path()), "stdin: OK\n");
    command = "\"" + std::string(tool) + "\" verify < \"" + empty_file_.path() +
              "\" > \"" + output.path() + "\" 2>&1";
    EXPECT_EQ(ExecuteCommandExitCode(command), 2);
  }
}

TEST_F(VerifyChainTest, OpenSSLCallerComparison) {
  const char *awslc = getenv("AWSLC_TOOL_PATH");
  const char *openssl = getenv("OPENSSL_TOOL_PATH");
  if (awslc == nullptr || openssl == nullptr) {
    GTEST_SKIP() << "AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH are required";
  }
  VerifyTempFile output;
  ASSERT_TRUE(output.Init());
  std::string suffix = " verify -CApath \"" + std::string(ca_dir_) +
                       "\" -verbose -purpose sslserver -untrusted \"" +
                       bundle_file_.path() + "\" \"" + bundle_file_.path() +
                       "\" > \"" + output.path() + "\" 2>&1";
  for (bool valid : {true, false}) {
    ASSERT_TRUE(SetVerifyEKU(leaf_.get(), valid ? "serverAuth" : "clientAuth",
                             intermediate_key_.get()));
    ASSERT_TRUE(WriteInputs());
    for (const char *tool : {awslc, openssl}) {
      SCOPED_TRACE(tool);
      int status =
          ExecuteCommandExitCode("\"" + std::string(tool) + "\"" + suffix);
      EXPECT_EQ(valid ? 0 : 2, status);
      std::string text = ReadVerifyOutput(output.path());
      if (valid) {
        EXPECT_EQ(text, bundle_file_.path() + ": OK\n");
      } else {
        // The wording differs ("unsupported" vs "unsuitable"), but the
        // verification error code and depth must match.
        EXPECT_NE(text.find("error 26 at 0 depth lookup:"), std::string::npos);
        EXPECT_NE(text.find("verification failed"), std::string::npos);
      }
    }
  }
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
