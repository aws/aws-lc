// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include "../crypto/test/test_util.h"
#include "internal.h"
#include "test_util.h"

#if !defined(OPENSSL_WINDOWS)
#include <dirent.h>
#include <openssl/pem.h>

#include <map>
#include <set>

struct FreeOpenSSLChar {
  void operator()(char *v) { OPENSSL_free(v); }
};

using ScopedCharBuffer = std::unique_ptr<char, FreeOpenSSLChar>;
using ScopedDIR = std::unique_ptr<DIR, int (*)(DIR *)>;

// Test fixture class
class RehashTest : public ::testing::Test {
 protected:
  BUCKET **hash_table = get_table();

  void makePathInDir(ScopedCharBuffer &full_path, const char *dir,
                     const char *filename) {
    size_t buffer_len = strlen(dir) + strlen(filename) + 2;
    char *buffer = (char *)OPENSSL_zalloc(sizeof(char) * buffer_len);
    if (buffer == nullptr) {
      abort();
    }
    full_path.reset(buffer);
    snprintf(full_path.get(), buffer_len, "%s/%s", dir, filename);
  }

  void SetUp() override {
    ASSERT_GT(createTempDirPath(test_dir), 0u);
    makePathInDir(cert1_path, test_dir, "cert1.pem");
    makePathInDir(cert2_path, test_dir, "cert2.pem");
    makePathInDir(crl1_path, test_dir, "crl1.pem");
    makePathInDir(crl2_path, test_dir, "crl2.pem");

    ScopedFILE in_file(fopen(cert1_path.get(), "wb"));
    bssl::UniquePtr<X509> x509;
    CreateAndSignX509Certificate(x509, nullptr);
    ASSERT_TRUE(x509);
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));

    ScopedFILE in_file2(fopen(cert2_path.get(), "wb"));
    CreateAndSignX509Certificate(x509, nullptr);
    ASSERT_TRUE(x509);
    ASSERT_TRUE(in_file2);
    ASSERT_TRUE(PEM_write_X509(in_file2.get(), x509.get()));

    bssl::UniquePtr<X509_CRL> crl(createTestCRL());
    ScopedFILE crl_file(fopen(crl1_path.get(), "wb"));
    ASSERT_TRUE(crl);
    ASSERT_TRUE(crl_file);
    ASSERT_TRUE(PEM_write_X509_CRL(crl_file.get(), crl.get()));

    crl.reset(createTestCRL());
    ScopedFILE crl_file2(fopen(crl2_path.get(), "wb"));
    ASSERT_TRUE(crl);
    ASSERT_TRUE(crl_file2);
    ASSERT_TRUE(PEM_write_X509_CRL(crl_file2.get(), crl.get()));
  }

  void TearDown() override {
    // Remove generated links too, including after a failed assertion.
    ScopedDIR dir(opendir(test_dir), closedir);
    ASSERT_TRUE(dir);
    while (struct dirent *entry = readdir(dir.get())) {
      std::string name = entry->d_name;
      if (name != "." && name != "..") {
        EXPECT_EQ(0, unlink((std::string(test_dir) + "/" + name).c_str()));
      }
    }
    dir.reset();
    EXPECT_EQ(0, rmdir(test_dir));
    cleanup_hash_table();
  }

  // Helper function to create test entries
  void CreateTestEntry(Type type, uint32_t hash, const char *filename,
                       uint8_t *digest) {
    add_entry(type, hash, filename, digest);
  }

  // Helper to count entries in a bucket
  size_t CountEntriesInBucket(BUCKET *bucket) {
    size_t count = 0;
    HASH_ENTRY *entry = bucket ? bucket->first_entry : nullptr;
    while (entry) {
      count++;
      entry = entry->next;
    }
    return count;
  }

  using LinkContents = std::multiset<std::pair<std::string, std::string>>;

  std::string Path(const std::string &name) {
    return std::string(test_dir) + "/" + name;
  }

  void WriteFile(const std::string &name, const std::string &contents) {
    ScopedFILE file(fopen(Path(name).c_str(), "wb"));
    ASSERT_TRUE(file);
    ASSERT_EQ(contents.size(),
              fwrite(contents.data(), 1, contents.size(), file.get()));
  }

  void ReadInputs(std::map<std::string, std::string> *inputs) {
    inputs->clear();
    ScopedDIR dir(opendir(test_dir), closedir);
    ASSERT_TRUE(dir);
    while (struct dirent *entry = readdir(dir.get())) {
      struct stat st;
      ASSERT_EQ(0, lstat(Path(entry->d_name).c_str(), &st));
      if (S_ISREG(st.st_mode)) {
        inputs->emplace(entry->d_name, ReadFileToString(Path(entry->d_name)));
      }
    }
  }

  // Compare resolved contents per hash/type, not suffix assignments or the
  // filenames chosen among duplicates: readdir order is unspecified.
  void ReadLinks(LinkContents *links) {
    links->clear();
    ScopedDIR dir(opendir(test_dir), closedir);
    ASSERT_TRUE(dir);
    while (struct dirent *entry = readdir(dir.get())) {
      std::string name = entry->d_name;
      struct stat st;
      ASSERT_EQ(0, lstat(Path(name).c_str(), &st));
      if (!S_ISLNK(st.st_mode)) {
        continue;
      }
      ASSERT_GE(name.size(), 10u);
      ASSERT_EQ(8u, name.find('.'));
      ASSERT_EQ(8u, name.find_first_not_of("0123456789abcdef"));
      size_t suffix = name[9] == 'r' ? 10 : 9;
      ASSERT_LT(suffix, name.size());
      ASSERT_EQ(std::string::npos,
                name.find_first_not_of("0123456789", suffix));
      char target[PATH_MAX];
      ssize_t len = readlink(Path(name).c_str(), target, sizeof(target));
      ASSERT_GT(len, 0);
      ASSERT_LT(static_cast<size_t>(len), sizeof(target));
      std::string filename(target, len);
      ASSERT_EQ(std::string::npos, filename.find('/'));
      ASSERT_EQ(0, lstat(Path(filename).c_str(), &st));
      ASSERT_TRUE(S_ISREG(st.st_mode));
      std::string contents = ReadFileToString(Path(name));
      ASSERT_FALSE(contents.empty());
      EXPECT_EQ(ReadFileToString(Path(filename)), contents);
      links->emplace(name.substr(0, suffix), contents);
    }
  }

  LinkContents ExpectedLinks(bool compat) {
    // Fixed name hashes corroborated with OpenSSL 1.1.1w. The certificate
    // subject is O=Org,CN=Name; the CRL issuer is CN=Test CA (UTF8Strings).
    LinkContents expected;
    for (const auto *path : {cert1_path.get(), cert2_path.get()}) {
      expected.emplace("80417837.", ReadFileToString(path));
      if (compat) {
        expected.emplace("55f64dd4.", ReadFileToString(path));
      }
    }
    for (const auto *path : {crl1_path.get(), crl2_path.get()}) {
      expected.emplace("3387b84d.r", ReadFileToString(path));
      if (compat) {
        expected.emplace("5ab8aa71.r", ReadFileToString(path));
      }
    }
    return expected;
  }

  void ExpectLinks(const LinkContents &expected) {
    LinkContents actual;
    ASSERT_NO_FATAL_FAILURE(ReadLinks(&actual));
    EXPECT_EQ(expected, actual);
  }

  ScopedCharBuffer cert1_path;
  ScopedCharBuffer cert2_path;
  ScopedCharBuffer crl1_path;
  ScopedCharBuffer crl2_path;
  char test_dir[PATH_MAX];
};

// Test hashtable Bucket collisions at an idx
TEST_F(RehashTest, BucketCollision) {
  // Create entries that would hash to same index but different type/hash
  uint32_t hash1 = 0x12345678;
  // Force collision for CRL and hash1
  uint32_t hash2 = hash1 - 1;
  // Force collision for another cert with hash1
  uint32_t hash3 = hash1 + 257;  // Adding 257 ensures same remainder

  // Verify these type+hash combos will collide on an idx
  uint32_t idx1 = (TYPE_CERT + hash1) % 257;
  uint32_t idx2 = (TYPE_CRL + hash2) % 257;
  uint32_t idx3 = (TYPE_CERT + hash3) % 257;
  ASSERT_EQ(idx1, idx2);
  ASSERT_EQ(idx2, idx3);

  // SHA_1 digest size
  uint8_t digest1[20] = {0x10};
  uint8_t digest2[20] = {0x20};
  uint8_t digest3[20] = {0x30};

  CreateTestEntry(TYPE_CERT, hash1, "cert.pem", digest1);
  CreateTestEntry(TYPE_CRL, hash2, "crl.pem", digest2);
  CreateTestEntry(TYPE_CERT, hash3, "cert2.pem", digest3);

  BUCKET *bucket = hash_table[idx1];
  ASSERT_NE(bucket, nullptr);

  // First bucket should be the most recently added
  EXPECT_EQ(bucket->type, TYPE_CERT);
  EXPECT_EQ(bucket->hash, hash3);
  EXPECT_STREQ(bucket->first_entry->filename, "cert2.pem");

  // Then CRL
  bucket = bucket->next;
  EXPECT_EQ(bucket->type, TYPE_CRL);
  EXPECT_EQ(bucket->hash, hash2);
  EXPECT_STREQ(bucket->first_entry->filename, "crl.pem");

  // Check last bucket in chain
  bucket = bucket->next;
  ASSERT_NE(bucket, nullptr);
  EXPECT_EQ(bucket->type, TYPE_CERT);
  EXPECT_EQ(bucket->hash, hash1);
  EXPECT_STREQ(bucket->first_entry->filename, "cert.pem");

  // Verify there are no more buckets at this idx
  bucket = bucket->next;
  ASSERT_EQ(bucket, nullptr);

  cleanup_hash_table();
}

// Test hashtable collisions within a bucket
TEST_F(RehashTest, EntryCollision) {
  // SHA_1 digest size
  uint8_t digest1[20] = {0x10};
  uint8_t digest2[20] = {0x20};
  uint8_t digest3[20] = {0x30};

  // Create multiple entries with same type and hash but different certs
  CreateTestEntry(TYPE_CERT, 0x12345678, "cert1.pem", digest1);
  CreateTestEntry(TYPE_CERT, 0x12345678, "cert2.pem", digest2);
  CreateTestEntry(TYPE_CERT, 0x12345678, "cert3.pem", digest3);

  // Try adding a duplicate cert (distinguished by digest)
  // but with a different filename
  CreateTestEntry(TYPE_CERT, 0x12345678, "cert4.pem", digest1);

  uint32_t expected_idx = (TYPE_CERT + 0x12345678) % 257;
  BUCKET *bucket = hash_table[expected_idx];

  ASSERT_NE(bucket, nullptr);
  EXPECT_EQ(bucket->num_entries, 3u);
  EXPECT_EQ(CountEntriesInBucket(bucket), 3u);

  // Verify entries are in correct order
  HASH_ENTRY *entry = bucket->first_entry;
  HASH_ENTRY *last = bucket->last_entry;
  EXPECT_STREQ(entry->filename, "cert1.pem");
  entry = entry->next;
  EXPECT_STREQ(entry->filename, "cert2.pem");
  entry = entry->next;
  EXPECT_STREQ(entry->filename, "cert3.pem");
  EXPECT_STREQ(last->filename, "cert3.pem");

  cleanup_hash_table();
}

TEST_F(RehashTest, CompatDirectory) {
  const auto expected = ExpectedLinks(true);
  std::map<std::string, std::string> before, after;
  ASSERT_NO_FATAL_FAILURE(ReadInputs(&before));
  ASSERT_EQ(kToolExitSuccess, RehashTool({"-compat", test_dir}));
  ExpectLinks(expected);
  ASSERT_NO_FATAL_FAILURE(ReadInputs(&after));
  EXPECT_EQ(before, after);
}

TEST_F(RehashTest, CompatDuplicatesCollisionsAndReruns) {
  const auto modern = ExpectedLinks(false);
  const auto compat = ExpectedLinks(true);
  ASSERT_NO_FATAL_FAILURE(
      WriteFile("duplicate.crt", ReadFileToString(cert1_path.get())));
  ASSERT_NO_FATAL_FAILURE(
      WriteFile("duplicate.crl", ReadFileToString(crl1_path.get())));
  std::map<std::string, std::string> before, after;
  ASSERT_NO_FATAL_FAILURE(ReadInputs(&before));

  ASSERT_EQ(kToolExitSuccess, RehashTool({test_dir}));
  ExpectLinks(modern);
  for (int i = 0; i < 2; i++) {
    ASSERT_EQ(kToolExitSuccess, RehashTool({"-compat", test_dir}));
    ExpectLinks(compat);
  }
  // The default invocation must remove legacy links and forget the mode from
  // the preceding calls in this same process.
  ASSERT_EQ(kToolExitSuccess, RehashTool({test_dir}));
  ExpectLinks(modern);
  ASSERT_NO_FATAL_FAILURE(ReadInputs(&after));
  EXPECT_EQ(before, after);
}

TEST_F(RehashTest, CompatNameNamespaces) {
  bssl::UniquePtr<X509> cert;
  bssl::UniquePtr<EVP_PKEY> key;
  CreateAndSignX509Certificate(cert, &key);
  ASSERT_TRUE(cert);
  ASSERT_TRUE(key);
  bssl::UniquePtr<X509_NAME> name(X509_NAME_new());
  ASSERT_TRUE(name);
  ASSERT_TRUE(X509_NAME_add_entry_by_txt(
      name.get(), "CN", MBSTRING_UTF8,
      reinterpret_cast<const uint8_t *>("Test Name"), -1, -1, 0));
  // Leave the issuer as O=Org,CN=Name to distinguish subject from issuer.
  ASSERT_TRUE(X509_set_subject_name(cert.get(), name.get()));
  ASSERT_TRUE(X509_sign(cert.get(), key.get(), EVP_sha256()));
  bssl::UniquePtr<X509_CRL> crl(createTestCRL());
  ASSERT_TRUE(crl);
  ASSERT_TRUE(X509_CRL_set_issuer_name(crl.get(), name.get()));
  ASSERT_TRUE(X509_CRL_sign(crl.get(), key.get(), EVP_sha256()));
  ScopedFILE cert_file(fopen(cert1_path.get(), "wb"));
  ScopedFILE crl_file(fopen(crl1_path.get(), "wb"));
  ASSERT_TRUE(cert_file);
  ASSERT_TRUE(crl_file);
  ASSERT_TRUE(PEM_write_X509(cert_file.get(), cert.get()));
  ASSERT_TRUE(PEM_write_X509_CRL(crl_file.get(), crl.get()));
  cert_file.reset();
  crl_file.reset();
  ASSERT_EQ(0, unlink(cert2_path.get()));
  ASSERT_EQ(0, unlink(crl2_path.get()));

  // These fixed values also appear in X509Test.NameHash. Certificates and
  // CRLs with the same name must occupy separate .N and .rN namespaces.
  LinkContents expected = {
      {"c90fba01.", ReadFileToString(cert1_path.get())},
      {"8c0d4fea.", ReadFileToString(cert1_path.get())},
      {"c90fba01.r", ReadFileToString(crl1_path.get())},
      {"8c0d4fea.r", ReadFileToString(crl1_path.get())},
  };
  ASSERT_EQ(kToolExitSuccess, RehashTool({"-compat", test_dir}));
  ExpectLinks(expected);
}

TEST_F(RehashTest, CompatExtensionsAndNonCertificates) {
  const auto expected = ExpectedLinks(true);
  ASSERT_NO_FATAL_FAILURE(
      WriteFile("ignored.der", ReadFileToString(cert1_path.get())));
  ASSERT_NO_FATAL_FAILURE(WriteFile("notes.txt", "not a certificate\n"));
  ASSERT_NO_FATAL_FAILURE(WriteFile("invalid.pem", "not a certificate\n"));
  ASSERT_NO_FATAL_FAILURE(WriteFile(
      "bundle.pem",
      ReadFileToString(cert1_path.get()) + ReadFileToString(cert2_path.get())));
  ASSERT_EQ(0, rename(cert1_path.get(), Path("cert1.crt").c_str()));
  ASSERT_EQ(0, rename(cert2_path.get(), Path("cert2.CER").c_str()));
  ASSERT_EQ(0, rename(crl1_path.get(), Path("crl1.crl").c_str()));
  ASSERT_EQ(0, symlink("missing.pem", Path("deadbeef.7").c_str()));
  ASSERT_EQ(0, symlink("missing.crl", Path("deadbeef.r7").c_str()));
  ASSERT_EQ(0, symlink("cert1.crt", Path("preserved-link").c_str()));
  std::map<std::string, std::string> before, after;
  ASSERT_NO_FATAL_FAILURE(ReadInputs(&before));
  ASSERT_EQ(kToolExitSuccess, RehashTool({"-compat", test_dir}));
  EXPECT_EQ(before["cert1.crt"], ReadFileToString(Path("preserved-link")));
  ASSERT_EQ(0, unlink(Path("preserved-link").c_str()));
  ExpectLinks(expected);
  ASSERT_NO_FATAL_FAILURE(ReadInputs(&after));
  EXPECT_EQ(before, after);
}

TEST_F(RehashTest, CompatInvalidArgumentsAndPaths) {
  struct {
    args_list_t args;
    const char *diagnostic;
  } tests[] = {
      {{"-compat", "-unknown", test_dir}, "Unknown flag: -unknown"},
      {{"-compat", test_dir, test_dir}, "-help"},
      {{"-compat", "true", test_dir}, "-help"},
      {{"-compat", Path("missing")}, "Unable to resolve directory path"},
      {{"-compat", cert1_path.get()}, "is not a directory"},
  };
  for (const auto &test : tests) {
    testing::internal::CaptureStderr();
    int result = RehashTool(test.args);
    std::string err = testing::internal::GetCapturedStderr();
    EXPECT_EQ(kToolExitFailure, result);
    EXPECT_NE(std::string::npos, err.find(test.diagnostic)) << err;
    ExpectLinks({});
  }
}

TEST_F(RehashTest, CompatLinkFailureAndRecovery) {
  const auto expected = ExpectedLinks(true);
  // An ordinary file at a legacy link name must not be overwritten, and
  // failure to create that link must be reported even if modern links succeed.
  ASSERT_NO_FATAL_FAILURE(WriteFile("55f64dd4.0", "keep this file\n"));
  testing::internal::CaptureStderr();
  int result = RehashTool({"-compat", test_dir});
  std::string err = testing::internal::GetCapturedStderr();
  EXPECT_EQ(kToolExitFailure, result);
  EXPECT_NE(std::string::npos, err.find("Error creating symlink '55f64dd4.0'"));
  EXPECT_EQ("keep this file\n", ReadFileToString(Path("55f64dd4.0")));
  ASSERT_EQ(0, unlink(Path("55f64dd4.0").c_str()));
  ASSERT_EQ(kToolExitSuccess, RehashTool({"-compat", test_dir}));
  ExpectLinks(expected);
  ASSERT_EQ(kToolExitSuccess, RehashTool({test_dir}));
  ExpectLinks(ExpectedLinks(false));
}

TEST_F(RehashTest, CompatComparison) {
  const char *tool = getenv("AWSLC_TOOL_PATH");
  const char *reference = getenv("OPENSSL_TOOL_PATH");
  if (tool == nullptr || reference == nullptr) {
    GTEST_SKIP() << "AWSLC_TOOL_PATH and OPENSSL_TOOL_PATH are required";
  }
  ASSERT_NO_FATAL_FAILURE(
      WriteFile("duplicate.pem", ReadFileToString(cert1_path.get())));
  ASSERT_NO_FATAL_FAILURE(
      WriteFile("duplicate.crl", ReadFileToString(crl1_path.get())));
  std::map<std::string, std::string> before, after;
  ASSERT_NO_FATAL_FAILURE(ReadInputs(&before));
  for (const char *executable : {reference, tool}) {
    for (bool compat : {false, true, true, false}) {
      SCOPED_TRACE(executable);
      SCOPED_TRACE(compat);
      std::string command = ShellEscape(executable) + " rehash " +
                            (compat ? "-compat " : "") + ShellEscape(test_dir);
      ASSERT_EQ(kToolExitSuccess, ExecuteCommandExitCode(command));
      ExpectLinks(ExpectedLinks(compat));
      ASSERT_NO_FATAL_FAILURE(ReadInputs(&after));
      EXPECT_EQ(before, after);
    }
  }
}

// Test -help
TEST_F(RehashTest, RehashHelp) {
  args_list_t args = {"-help"};
  testing::internal::CaptureStderr();
  int result = RehashTool(args);
  std::string help = testing::internal::GetCapturedStderr();
  ASSERT_EQ(kToolExitSuccess, result);
  EXPECT_NE(std::string::npos, help.find("-compat"));
  EXPECT_NE(std::string::npos, help.find("SHA-1"));
  EXPECT_NE(std::string::npos, help.find("MD5"));
}

TEST_F(RehashTest, InvalidDirectory) {
  errno = 0;
  args_list_t args = {"/random/dir"};
  int result = RehashTool(args);
  ASSERT_EQ(kToolExitFailure, result);
  ASSERT_EQ(errno, ENOENT);
}

TEST_F(RehashTest, MoreThanOneDirectory) {
  errno = 0;
  args_list_t args = {"/random/dir", "/random/dir2"};
  int result = RehashTool(args);
  ASSERT_EQ(kToolExitFailure, result);
  // errno should not be set
  ASSERT_EQ(errno, 0);
}

// We cannot force the order in which rehash processes files from the given
// directory. Therefore, we cannot deterministically know the symlink # suffix
// for a given filename. We only check that the correct symlinks exist, with
// the correct hash value, and the correct suffix ("r" vs "") for CRL vs CERT.
// We do not verify the number suffix.
TEST_F(RehashTest, ValidDirectory) {
  args_list_t args = {test_dir};
  int result = RehashTool(args);
  ASSERT_EQ(kToolExitSuccess, result);

  // Get hashes for certs and CRLs
  ScopedFILE cert_file(fopen(cert1_path.get(), "rb"));
  bssl::UniquePtr<X509> cert(
      PEM_read_X509(cert_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(cert);
  uint32_t cert_hash = X509_subject_name_hash(cert.get());

  ScopedFILE crl_file(fopen(crl1_path.get(), "rb"));
  bssl::UniquePtr<X509_CRL> crl(
      PEM_read_X509_CRL(crl_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(crl);
  uint32_t crl_hash = X509_NAME_hash(X509_CRL_get_issuer(crl.get()));

  // Check that symlinks exist with correct format and targets
  size_t link_path_len =
      strlen(test_dir) + 13;  // 13 = slash + hex + decimal + char + int + nul
  ScopedCharBuffer link_path(
      (char *)OPENSSL_zalloc(sizeof(char) * link_path_len));
  char link_target[PATH_MAX];
  struct stat st;

  // Cleanup symlinks as we check them so directory teardown can proceed

  // Check cert symlinks (should have .0 and .1 suffixes)
  for (int i = 0; i < 2; i++) {
    snprintf(link_path.get(), link_path_len, "%s/%08x.%d", test_dir, cert_hash,
             i);
    ASSERT_EQ(0, lstat(link_path.get(), &st));
    ASSERT_TRUE(S_ISLNK(st.st_mode));

    ssize_t len =
        readlink(link_path.get(), link_target, sizeof(link_target) - 1);
    ASSERT_GT(len, 0);
    link_target[len] = '\0';
    ASSERT_TRUE(strstr(link_target, "cert") != nullptr);
    unlink(link_path.get());
  }

  // Check CRL symlinks (should have .r0 and .r1 suffixes)
  for (int i = 0; i < 2; i++) {
    snprintf(link_path.get(), link_path_len, "%s/%08x.r%d", test_dir, crl_hash,
             i);
    ASSERT_EQ(0, lstat(link_path.get(), &st));
    ASSERT_TRUE(S_ISLNK(st.st_mode));

    ssize_t len =
        readlink(link_path.get(), link_target, sizeof(link_target) - 1);
    ASSERT_GT(len, 0);
    link_target[len] = '\0';
    ASSERT_TRUE(strstr(link_target, "crl") != nullptr);
    unlink(link_path.get());
  }
}
#else

TEST(TmpDir, CreateTmpDir) {
  char tempdir[PATH_MAX];

  // Test directory creation
  size_t len = createTempDirPath(tempdir);
  ASSERT_GT(len, 0u);

  // Verify directory exists
  DWORD attrs = GetFileAttributesA(tempdir);
  EXPECT_NE(attrs, INVALID_FILE_ATTRIBUTES);
  EXPECT_TRUE(attrs & FILE_ATTRIBUTE_DIRECTORY);

  // Test we can create a file in the directory
  char testfile[PATH_MAX];
  snprintf(testfile, PATH_MAX, "%s\\test.txt", tempdir);
  FILE *f = fopen(testfile, "w");
  ASSERT_TRUE(f != nullptr);
  fprintf(f, "test");
  fclose(f);

  // Cleanup
  DeleteFileA(testfile);                   // Delete test file
  EXPECT_TRUE(RemoveDirectoryA(tempdir));  // Delete directory
}

#endif
