// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"
#include "../crypto/test/test_util.h"
#include "test_util.h"
#include <gtest/gtest.h>

#if !defined(OPENSSL_WINDOWS)
#include <openssl/pem.h>

// Test fixture class
class RehashTest : public ::testing::Test {
protected:
  BUCKET** hash_table = get_table();

  void makePathInDir(char *full_path, const char *dir, const char *filename) {
    snprintf(full_path, 255, "%s/%s", dir, filename);
  }

  void SetUp() override {
    ASSERT_GT(createTempDirPath(test_dir), 0u);
    makePathInDir(cert1_path, test_dir, "cert1.pem");
    makePathInDir(cert2_path, test_dir, "cert2.pem");
    makePathInDir(crl1_path, test_dir, "crl1.pem");
    makePathInDir(crl2_path, test_dir, "crl2.pem");

    ScopedFILE in_file(fopen(cert1_path, "wb"));
    bssl::UniquePtr<X509> x509(CreateAndSignX509Certificate());
    ASSERT_TRUE(x509);
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));

    ScopedFILE in_file2(fopen(cert2_path, "wb"));
    x509.reset(CreateAndSignX509Certificate());
    ASSERT_TRUE(x509);
    ASSERT_TRUE(in_file2);
    ASSERT_TRUE(PEM_write_X509(in_file2.get(), x509.get()));

    bssl::UniquePtr<X509_CRL> crl(createTestCRL());
    ScopedFILE crl_file(fopen(crl1_path, "wb"));
    ASSERT_TRUE(crl);
    ASSERT_TRUE(crl_file);
    ASSERT_TRUE(PEM_write_X509_CRL(crl_file.get(), crl.get()));

    crl.reset(createTestCRL());
    ScopedFILE crl_file2(fopen(crl2_path, "wb"));
    ASSERT_TRUE(crl);
    ASSERT_TRUE(crl_file2);
    ASSERT_TRUE(PEM_write_X509_CRL(crl_file2.get(), crl.get()));
  }

  void TearDown() override {
    RemoveFile(cert1_path);
    RemoveFile(cert2_path);
    RemoveFile(crl1_path);
    RemoveFile(crl2_path);
    rmdir(test_dir);
  }

  // Helper function to create test entries
  void CreateTestEntry(Type type, uint32_t hash, const char* filename,
    uint8_t* digest) {
    add_entry(type, hash, filename, digest);
  }

  // Helper to count entries in a bucket
  size_t CountEntriesInBucket(BUCKET* bucket) {
    size_t count = 0;
    HASH_ENTRY* entry = bucket ? bucket->first_entry : nullptr;
    while (entry) {
      count++;
      entry = entry->next;
    }
    return count;
  }

  char cert1_path[256];
  char cert2_path[256];
  char crl1_path[256];
  char crl2_path[256];
  char test_dir[128];
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

  BUCKET* bucket = hash_table[idx1];
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
  BUCKET* bucket = hash_table[expected_idx];

  ASSERT_NE(bucket, nullptr);
  EXPECT_EQ(bucket->num_entries, 3u);
  EXPECT_EQ(CountEntriesInBucket(bucket), 3u);

  // Verify entries are in correct order
  HASH_ENTRY* entry = bucket->first_entry;
  HASH_ENTRY* last = bucket->last_entry;
  EXPECT_STREQ(entry->filename, "cert1.pem");
  entry = entry->next;
  EXPECT_STREQ(entry->filename, "cert2.pem");
  entry = entry->next;
  EXPECT_STREQ(entry->filename, "cert3.pem");
  EXPECT_STREQ(last->filename, "cert3.pem");

  cleanup_hash_table();
}

// Test -help
TEST_F(RehashTest, RehashHelp) {
  args_list_t args = {"-help"};
  bool result = RehashTool(args);
  ASSERT_FALSE(result);
}

TEST_F(RehashTest, InvalidDirectory) {
  errno = 0;
  args_list_t args = {"/random/dir"};
  bool result = RehashTool(args);
  ASSERT_FALSE(result);
  ASSERT_EQ(errno, ENOENT);
}

TEST_F(RehashTest, MoreThanOneDirectory) {
  errno = 0;
  args_list_t args = {"/random/dir", "/random/dir2"};
  bool result = RehashTool(args);
  ASSERT_FALSE(result);
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
  bool result = RehashTool(args);
  ASSERT_TRUE(result);

  // Get hashes for certs and CRLs
  ScopedFILE cert_file(fopen(cert1_path, "rb"));
  bssl::UniquePtr<X509> cert(PEM_read_X509(
    cert_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(cert);
  uint32_t cert_hash = X509_subject_name_hash(cert.get());

  ScopedFILE crl_file(fopen(crl1_path, "rb"));
  bssl::UniquePtr<X509_CRL> crl(PEM_read_X509_CRL(
    crl_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(crl);
  uint32_t crl_hash = X509_NAME_hash(X509_CRL_get_issuer(crl.get()));

  // Check that symlinks exist with correct format and targets
  char link_path[PATH_MAX];
  char link_target[PATH_MAX];
  struct stat st;

  // Cleanup symlinks as we check them so directory teardown can proceed

  // Check cert symlinks (should have .0 and .1 suffixes)
  for (int i = 0; i < 2; i++) {
    snprintf(link_path, sizeof(link_path), "%s/%08x.%d",
      test_dir, cert_hash, i);
    ASSERT_EQ(0, lstat(link_path, &st));
    ASSERT_TRUE(S_ISLNK(st.st_mode));

    ssize_t len = readlink(link_path, link_target, sizeof(link_target) - 1);
    ASSERT_GT(len, 0);
    link_target[len] = '\0';
    ASSERT_TRUE(strstr(link_target, "cert") != nullptr);
    unlink(link_path);
  }

  // Check CRL symlinks (should have .r0 and .r1 suffixes)
  for (int i = 0; i < 2; i++) {
    snprintf(link_path, sizeof(link_path), "%s/%08x.r%d",
      test_dir, crl_hash, i);
    ASSERT_EQ(0, lstat(link_path, &st));
    ASSERT_TRUE(S_ISLNK(st.st_mode));

    ssize_t len = readlink(link_path, link_target, sizeof(link_target) - 1);
    ASSERT_GT(len, 0);
    link_target[len] = '\0';
    ASSERT_TRUE(strstr(link_target, "crl") != nullptr);\
    unlink(link_path);
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
  FILE* f = fopen(testfile, "w");
  ASSERT_TRUE(f != nullptr);
  fprintf(f, "test");
  fclose(f);

  // Cleanup
  DeleteFileA(testfile);  // Delete test file
  EXPECT_TRUE(RemoveDirectoryA(tempdir));  // Delete directory
}

#endif
