/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC
 */

#include "txt_db.h"

#include <openssl/bio.h>
#include <openssl/mem.h>

#include <gtest/gtest.h>

#include <cstring>
#include <string>

// Helper function to create a hash for string fields
static unsigned int string_hash(const OPENSSL_STRING *str) {
  return static_cast<unsigned int>(OPENSSL_strhash(str[0]));
}

// Helper function to compare string fields
static int string_cmp(const OPENSSL_STRING *a, const OPENSSL_STRING *b) {
  return strcmp(a[0], b[0]);
}

// Test fixture for TXT_DB tests
class TxtDbTest : public ::testing::Test {
 protected:
  void SetUp() override {}
  void TearDown() override {}
};

// Test reading an empty database
TEST_F(TxtDbTest, ReadEmptyDatabase) {
  const char *empty_data = "";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(empty_data, strlen(empty_data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 3);
  ASSERT_TRUE(db);
  EXPECT_EQ(db->num_fields, 3);
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 0u);
}

// Test reading a database with comment lines
TEST_F(TxtDbTest, ReadDatabaseWithComments) {
  const char *data = "# This is a comment\n"
                     "field1\tfield2\tfield3\n"
                     "# Another comment\n"
                     "value1\tvalue2\tvalue3\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 3);
  ASSERT_TRUE(db);
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 2u);

  // Verify first row (non-comment)
  OPENSSL_STRING *row0 = sk_OPENSSL_PSTRING_value(db->data, 0);
  EXPECT_STREQ(row0[0], "field1");
  EXPECT_STREQ(row0[1], "field2");
  EXPECT_STREQ(row0[2], "field3");

  // Verify second row (non-comment)
  OPENSSL_STRING *row1 = sk_OPENSSL_PSTRING_value(db->data, 1);
  EXPECT_STREQ(row1[0], "value1");
  EXPECT_STREQ(row1[1], "value2");
  EXPECT_STREQ(row1[2], "value3");
}

// Test reading a database with escaped tabs
TEST_F(TxtDbTest, ReadDatabaseWithEscapedTabs) {
  const char *data = "field\\twith\\ttabs\tfield2\tfield3\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 3);
  ASSERT_TRUE(db);
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 1u);

  OPENSSL_STRING *row = sk_OPENSSL_PSTRING_value(db->data, 0);
  // The backslash-t sequences are preserved as-is in the string
  EXPECT_STREQ(row[0], "field\\twith\\ttabs");
  EXPECT_STREQ(row[1], "field2");
  EXPECT_STREQ(row[2], "field3");
}

// Test reading a database with wrong number of fields
TEST_F(TxtDbTest, ReadDatabaseWrongNumFields) {
  const char *data = "field1\tfield2\n";  // Only 2 fields, expecting 3
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 3);
  EXPECT_FALSE(db);
}

// Test reading a database with too many fields
TEST_F(TxtDbTest, ReadDatabaseTooManyFields) {
  const char *data = "field1\tfield2\tfield3\tfield4\n";  // 4 fields, expecting 3
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 3);
  EXPECT_FALSE(db);
}

// Test writing a database
TEST_F(TxtDbTest, WriteDatabase) {
  const char *data = "field1\tfield2\tfield3\n"
                     "value1\tvalue2\tvalue3\n";
  bssl::UniquePtr<BIO> read_bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(read_bio);

  auto db = TXT_DB_read(read_bio, 3);
  ASSERT_TRUE(db);

  bssl::UniquePtr<BIO> write_bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(write_bio);

  long written = TXT_DB_write(write_bio, db);
  EXPECT_GT(written, 0);

  // Read back the written data
  char *buf = nullptr;
  long len = BIO_get_mem_data(write_bio.get(), &buf);
  std::string output(buf, len);

  // Verify the output contains our data
  EXPECT_TRUE(output.find("field1") != std::string::npos);
  EXPECT_TRUE(output.find("value1") != std::string::npos);
}

// Test writing a database with tabs in fields (should be escaped)
TEST_F(TxtDbTest, WriteDatabaseWithTabs) {
  const char *data = "field\\twith\\ttabs\tfield2\tfield3\n";
  bssl::UniquePtr<BIO> read_bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(read_bio);

  auto db = TXT_DB_read(read_bio, 3);
  ASSERT_TRUE(db);

  bssl::UniquePtr<BIO> write_bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(write_bio);

  long written = TXT_DB_write(write_bio, db);
  EXPECT_GT(written, 0);

  // Read back and verify tabs are escaped
  char *buf = nullptr;
  long len = BIO_get_mem_data(write_bio.get(), &buf);
  std::string output(buf, len);

  // The output should contain escaped tabs
  EXPECT_TRUE(output.find("\\t") != std::string::npos);
}

// Test creating an index
TEST_F(TxtDbTest, CreateIndex) {
  const char *data = "key1\tvalue1\n"
                     "key2\tvalue2\n"
                     "key3\tvalue3\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Create index on first field
  EXPECT_TRUE(TXT_DB_create_index(db, 0, nullptr, string_hash, string_cmp));
  EXPECT_TRUE(db->index[0] != nullptr);
}

// Test creating an index on out-of-range field
TEST_F(TxtDbTest, CreateIndexOutOfRange) {
  const char *data = "key1\tvalue1\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Try to create index on field 5 (out of range)
  EXPECT_FALSE(TXT_DB_create_index(db, 5, nullptr, string_hash, string_cmp));
  EXPECT_EQ(db->error, DB_ERROR_INDEX_OUT_OF_RANGE);
}

// Test creating an index with duplicate keys
TEST_F(TxtDbTest, CreateIndexWithDuplicates) {
  const char *data = "key1\tvalue1\n"
                     "key1\tvalue2\n";  // Duplicate key
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Create index on first field - should fail due to duplicates
  EXPECT_FALSE(TXT_DB_create_index(db, 0, nullptr, string_hash, string_cmp));
  EXPECT_EQ(db->error, DB_ERROR_INDEX_CLASH);
}

// Test getting by index
TEST_F(TxtDbTest, GetByIndex) {
  const char *data = "key1\tvalue1\n"
                     "key2\tvalue2\n"
                     "key3\tvalue3\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Create index on first field
  ASSERT_TRUE(TXT_DB_create_index(db, 0, nullptr, string_hash, string_cmp));

  // Search for key2
  const char *search_key = "key2";
  OPENSSL_STRING search_row[2] = {const_cast<char *>(search_key), nullptr};
  
  OPENSSL_STRING *result = TXT_DB_get_by_index(db, 0, search_row);
  ASSERT_TRUE(result);
  EXPECT_STREQ(result[0], "key2");
  EXPECT_STREQ(result[1], "value2");
}

// Test getting by index with non-existent key
TEST_F(TxtDbTest, GetByIndexNotFound) {
  const char *data = "key1\tvalue1\n"
                     "key2\tvalue2\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Create index on first field
  ASSERT_TRUE(TXT_DB_create_index(db, 0, nullptr, string_hash, string_cmp));

  // Search for non-existent key
  const char *search_key = "nonexistent";
  OPENSSL_STRING search_row[2] = {const_cast<char *>(search_key), nullptr};
  
  OPENSSL_STRING *result = TXT_DB_get_by_index(db, 0, search_row);
  EXPECT_FALSE(result);
  EXPECT_EQ(db->error, DB_ERROR_OK);
}

// Test getting by index without index created
TEST_F(TxtDbTest, GetByIndexNoIndex) {
  const char *data = "key1\tvalue1\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Try to get without creating index first
  const char *search_key = "key1";
  OPENSSL_STRING search_row[2] = {const_cast<char *>(search_key), nullptr};
  
  OPENSSL_STRING *result = TXT_DB_get_by_index(db, 0, search_row);
  EXPECT_FALSE(result);
  EXPECT_EQ(db->error, DB_ERROR_NO_INDEX);
}

// Test getting by out-of-range index
TEST_F(TxtDbTest, GetByIndexOutOfRange) {
  const char *data = "key1\tvalue1\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  const char *search_key = "key1";
  OPENSSL_STRING search_row[2] = {const_cast<char *>(search_key), nullptr};
  
  OPENSSL_STRING *result = TXT_DB_get_by_index(db, 10, search_row);
  EXPECT_FALSE(result);
  EXPECT_EQ(db->error, DB_ERROR_INDEX_OUT_OF_RANGE);
}

// Test inserting a row
TEST_F(TxtDbTest, InsertRow) {
  const char *data = "key1\tvalue1\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 1u);

  // Allocate a new row
  OPENSSL_STRING *new_row = (OPENSSL_STRING *)OPENSSL_malloc(sizeof(OPENSSL_STRING) * 3);
  ASSERT_TRUE(new_row);
  new_row[0] = OPENSSL_strdup("key2");
  new_row[1] = OPENSSL_strdup("value2");
  new_row[2] = nullptr;  // Mark as new row (max == NULL)

  EXPECT_TRUE(TXT_DB_insert(db, new_row));
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 2u);

  // Verify the inserted row
  OPENSSL_STRING *row1 = sk_OPENSSL_PSTRING_value(db->data, 1);
  EXPECT_STREQ(row1[0], "key2");
  EXPECT_STREQ(row1[1], "value2");
}

// Test inserting a row with index clash
TEST_F(TxtDbTest, InsertRowIndexClash) {
  const char *data = "key1\tvalue1\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Create index on first field
  ASSERT_TRUE(TXT_DB_create_index(db, 0, nullptr, string_hash, string_cmp));

  // Try to insert a row with duplicate key
  OPENSSL_STRING *new_row = (OPENSSL_STRING *)OPENSSL_malloc(sizeof(OPENSSL_STRING) * 3);
  ASSERT_TRUE(new_row);
  new_row[0] = OPENSSL_strdup("key1");  // Duplicate key
  new_row[1] = OPENSSL_strdup("value2");
  new_row[2] = nullptr;

  EXPECT_FALSE(TXT_DB_insert(db, new_row));
  EXPECT_EQ(db->error, DB_ERROR_INDEX_CLASH);

  // Clean up the failed insertion's memory
  OPENSSL_free(new_row[0]);
  OPENSSL_free(new_row[1]);
  OPENSSL_free(new_row);
}

// Test inserting a row and then retrieving it
TEST_F(TxtDbTest, InsertAndRetrieve) {
  const char *data = "key1\tvalue1\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Create index on first field
  ASSERT_TRUE(TXT_DB_create_index(db, 0, nullptr, string_hash, string_cmp));

  // Insert a new row
  OPENSSL_STRING *new_row = (OPENSSL_STRING *)OPENSSL_malloc(sizeof(OPENSSL_STRING) * 3);
  ASSERT_TRUE(new_row);
  new_row[0] = OPENSSL_strdup("key2");
  new_row[1] = OPENSSL_strdup("value2");
  new_row[2] = nullptr;

  EXPECT_TRUE(TXT_DB_insert(db, new_row));

  // Now retrieve the inserted row
  const char *search_key = "key2";
  OPENSSL_STRING search_row[2] = {const_cast<char *>(search_key), nullptr};
  
  OPENSSL_STRING *result = TXT_DB_get_by_index(db, 0, search_row);
  ASSERT_TRUE(result);
  EXPECT_STREQ(result[0], "key2");
  EXPECT_STREQ(result[1], "value2");
}

// Test creating an index with qualifier function
static int qualifier_skip_odd(OPENSSL_STRING *row) {
  // Skip rows where the first character is odd digit
  if (row[0] && row[0][0] >= '1' && row[0][0] <= '9') {
    int digit = row[0][0] - '0';
    return (digit % 2 == 0) ? 1 : 0;  // Only include even
  }
  return 1;  // Include by default
}

TEST_F(TxtDbTest, CreateIndexWithQualifier) {
  const char *data = "1key\tvalue1\n"
                     "2key\tvalue2\n"
                     "3key\tvalue3\n"
                     "4key\tvalue4\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Create index with qualifier - only even numbered rows will be indexed
  ASSERT_TRUE(TXT_DB_create_index(db, 0, qualifier_skip_odd, string_hash, string_cmp));

  // Search for 2key (should be found)
  const char *search_key2 = "2key";
  OPENSSL_STRING search_row2[2] = {const_cast<char *>(search_key2), nullptr};
  OPENSSL_STRING *result2 = TXT_DB_get_by_index(db, 0, search_row2);
  ASSERT_TRUE(result2);
  EXPECT_STREQ(result2[1], "value2");

  // Search for 1key (should NOT be found - odd)
  const char *search_key1 = "1key";
  OPENSSL_STRING search_row1[2] = {const_cast<char *>(search_key1), nullptr};
  OPENSSL_STRING *result1 = TXT_DB_get_by_index(db, 0, search_row1);
  EXPECT_FALSE(result1);
}

// Test reading multiple rows
TEST_F(TxtDbTest, ReadMultipleRows) {
  const char *data = "V\t20251231000000Z\t\t01\tunknown\t/CN=test1\n"
                     "V\t20251231000000Z\t\t02\tunknown\t/CN=test2\n"
                     "R\t20241231000000Z\t20231231000000Z\t03\tunknown\t/CN=revoked\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 6);
  ASSERT_TRUE(db);
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 3u);

  // Verify first row
  OPENSSL_STRING *row0 = sk_OPENSSL_PSTRING_value(db->data, 0);
  EXPECT_STREQ(row0[0], "V");
  EXPECT_STREQ(row0[5], "/CN=test1");

  // Verify revoked row
  OPENSSL_STRING *row2 = sk_OPENSSL_PSTRING_value(db->data, 2);
  EXPECT_STREQ(row2[0], "R");
  EXPECT_STREQ(row2[5], "/CN=revoked");
}

// Test freeing NULL database
TEST_F(TxtDbTest, FreeNullDatabase) {
  // Should not crash
  TXT_DB_free(nullptr);
}

// Test round-trip (read, write, read again)
TEST_F(TxtDbTest, RoundTrip) {
  const char *original_data = "key1\tvalue1\n"
                              "key2\tvalue2\n"
                              "key3\tvalue3\n";
  bssl::UniquePtr<BIO> read_bio(BIO_new_mem_buf(original_data, strlen(original_data)));
  ASSERT_TRUE(read_bio);

  auto db1 = TXT_DB_read(read_bio, 2);
  ASSERT_TRUE(db1);

  // Write to memory BIO
  bssl::UniquePtr<BIO> write_bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(write_bio);
  long written = TXT_DB_write(write_bio, db1);
  EXPECT_GT(written, 0);

  // Read from the written data
  char *buf = nullptr;
  long len = BIO_get_mem_data(write_bio.get(), &buf);
  
  bssl::UniquePtr<BIO> read_bio2(BIO_new_mem_buf(buf, len));
  ASSERT_TRUE(read_bio2);

  auto db2 = TXT_DB_read(read_bio2, 2);
  ASSERT_TRUE(db2);
  
  // Verify the databases have the same content
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db1->data), sk_OPENSSL_PSTRING_num(db2->data));
  
  for (size_t i = 0; i < sk_OPENSSL_PSTRING_num(db1->data); i++) {
    OPENSSL_STRING *row1 = sk_OPENSSL_PSTRING_value(db1->data, i);
    OPENSSL_STRING *row2 = sk_OPENSSL_PSTRING_value(db2->data, i);
    
    for (size_t j = 0; j < static_cast<size_t>(db1->num_fields); j++) {
      EXPECT_STREQ(row1[j], row2[j]);
    }
  }
}

// Test reading database with empty fields
TEST_F(TxtDbTest, ReadDatabaseWithEmptyFields) {
  const char *data = "key1\t\tvalue3\n"
                     "\tvalue2\tvalue3\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 3);
  ASSERT_TRUE(db);
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 2u);

  // First row has empty middle field
  OPENSSL_STRING *row0 = sk_OPENSSL_PSTRING_value(db->data, 0);
  EXPECT_STREQ(row0[0], "key1");
  EXPECT_STREQ(row0[1], "");
  EXPECT_STREQ(row0[2], "value3");

  // Second row has empty first field
  OPENSSL_STRING *row1 = sk_OPENSSL_PSTRING_value(db->data, 1);
  EXPECT_STREQ(row1[0], "");
  EXPECT_STREQ(row1[1], "value2");
  EXPECT_STREQ(row1[2], "value3");
}

// Test replacing an index
TEST_F(TxtDbTest, ReplaceIndex) {
  const char *data = "key1\tvalueA\n"
                     "key2\tvalueB\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Create index on first field
  ASSERT_TRUE(TXT_DB_create_index(db, 0, nullptr, string_hash, string_cmp));

  // Verify it works
  const char *search_key = "key1";
  OPENSSL_STRING search_row[2] = {const_cast<char *>(search_key), nullptr};
  OPENSSL_STRING *result = TXT_DB_get_by_index(db, 0, search_row);
  ASSERT_TRUE(result);
  EXPECT_STREQ(result[1], "valueA");

  // Create a new index on the same field (should replace the old one)
  ASSERT_TRUE(TXT_DB_create_index(db, 0, nullptr, string_hash, string_cmp));

  // Verify it still works
  result = TXT_DB_get_by_index(db, 0, search_row);
  ASSERT_TRUE(result);
  EXPECT_STREQ(result[1], "valueA");
}

// Helper hash function for field 3 (serial number in CA database)
static unsigned int string_hash_field3(const OPENSSL_STRING *str) {
  return static_cast<unsigned int>(OPENSSL_strhash(str[3]));
}

// Helper compare function for field 3
static int string_cmp_field3(const OPENSSL_STRING *a, const OPENSSL_STRING *b) {
  return strcmp(a[3], b[3]);
}

// Test with CA database format (6 fields typical for OpenSSL CA)
TEST_F(TxtDbTest, CADatabaseFormat) {
  // Format: status\texpiry\trevocation\tserial\tfilename\tDN
  const char *data = "V\t250101000000Z\t\t01\tunknown\t/CN=Valid Cert\n"
                     "R\t250101000000Z\t240601000000Z\t02\tunknown\t/CN=Revoked Cert\n"
                     "E\t230101000000Z\t\t03\tunknown\t/CN=Expired Cert\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 6);
  ASSERT_TRUE(db);
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 3u);
  EXPECT_EQ(db->num_fields, 6);

  // Create index on serial number (field 3) with field 3-specific hash/cmp
  ASSERT_TRUE(TXT_DB_create_index(db, 3, nullptr, string_hash_field3, string_cmp_field3));

  // Look up by serial number - the hash function uses field 3
  const char *search_serial = "02";
  OPENSSL_STRING search_row[6] = {nullptr, nullptr, nullptr, 
                                   const_cast<char *>(search_serial), 
                                   nullptr, nullptr};
  
  OPENSSL_STRING *result = TXT_DB_get_by_index(db, 3, search_row);
  ASSERT_TRUE(result);
  EXPECT_STREQ(result[0], "R");  // Status should be Revoked
  EXPECT_STREQ(result[5], "/CN=Revoked Cert");
}

// Test inserting with qualifier during insert
TEST_F(TxtDbTest, InsertWithQualifier) {
  const char *data = "2key\tvalue2\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Create index with qualifier - only even numbered rows will be indexed
  ASSERT_TRUE(TXT_DB_create_index(db, 0, qualifier_skip_odd, string_hash, string_cmp));

  // Insert a row that should be skipped by qualifier (odd)
  OPENSSL_STRING *odd_row = (OPENSSL_STRING *)OPENSSL_malloc(sizeof(OPENSSL_STRING) * 3);
  ASSERT_TRUE(odd_row);
  odd_row[0] = OPENSSL_strdup("1key");  // Odd - will be skipped by qualifier
  odd_row[1] = OPENSSL_strdup("value1");
  odd_row[2] = nullptr;

  // This should succeed because the row is not indexed (skipped by qualifier)
  EXPECT_TRUE(TXT_DB_insert(db, odd_row));

  // Insert a row that would clash if indexed (even) - but with different key
  OPENSSL_STRING *even_row = (OPENSSL_STRING *)OPENSSL_malloc(sizeof(OPENSSL_STRING) * 3);
  ASSERT_TRUE(even_row);
  even_row[0] = OPENSSL_strdup("4key");  // Even - will be indexed
  even_row[1] = OPENSSL_strdup("value4");
  even_row[2] = nullptr;

  EXPECT_TRUE(TXT_DB_insert(db, even_row));
  
  // Verify both rows were inserted
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 3u);
}

// Test single field database
TEST_F(TxtDbTest, SingleFieldDatabase) {
  const char *data = "value1\n"
                     "value2\n"
                     "value3\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 1);
  ASSERT_TRUE(db);
  EXPECT_EQ(db->num_fields, 1);
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 3u);

  OPENSSL_STRING *row0 = sk_OPENSSL_PSTRING_value(db->data, 0);
  EXPECT_STREQ(row0[0], "value1");
}

// Test writing empty database
TEST_F(TxtDbTest, WriteEmptyDatabase) {
  const char *empty_data = "";
  bssl::UniquePtr<BIO> read_bio(BIO_new_mem_buf(empty_data, strlen(empty_data)));
  ASSERT_TRUE(read_bio);

  auto db = TXT_DB_read(read_bio, 2);
  ASSERT_TRUE(db);

  bssl::UniquePtr<BIO> write_bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(write_bio);

  long written = TXT_DB_write(write_bio, db);
  EXPECT_EQ(written, 0);  // Empty database should write 0 bytes
}

// Helper hash function for field 1
static unsigned int string_hash_field1(const OPENSSL_STRING *str) {
  return static_cast<unsigned int>(OPENSSL_strhash(str[1]));
}

// Helper compare function for field 1
static int string_cmp_field1(const OPENSSL_STRING *a, const OPENSSL_STRING *b) {
  return strcmp(a[1], b[1]);
}

// Test multiple indexes on different fields
TEST_F(TxtDbTest, MultipleIndexes) {
  const char *data = "key1\tval_a\n"
                     "key2\tval_b\n"
                     "key3\tval_c\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Create index on first field (field 0) with field 0 hash/cmp
  ASSERT_TRUE(TXT_DB_create_index(db, 0, nullptr, string_hash, string_cmp));
  
  // Create index on second field (field 1) with field 1 hash/cmp
  ASSERT_TRUE(TXT_DB_create_index(db, 1, nullptr, string_hash_field1, string_cmp_field1));

  // Search by first field
  const char *search_key1 = "key2";
  OPENSSL_STRING search_row1[2] = {const_cast<char *>(search_key1), nullptr};
  OPENSSL_STRING *result1 = TXT_DB_get_by_index(db, 0, search_row1);
  ASSERT_TRUE(result1);
  EXPECT_STREQ(result1[1], "val_b");

  // Search by second field
  const char *search_key2 = "val_c";
  OPENSSL_STRING search_row2[2] = {nullptr, const_cast<char *>(search_key2)};
  OPENSSL_STRING *result2 = TXT_DB_get_by_index(db, 1, search_row2);
  ASSERT_TRUE(result2);
  EXPECT_STREQ(result2[0], "key3");
}

// Test long lines requiring buffer growth
TEST_F(TxtDbTest, LongLines) {
  // Create a very long field value
  std::string long_value(1000, 'x');
  std::string data = long_value + "\tshort\n";
  
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data.c_str(), data.length()));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 1u);

  OPENSSL_STRING *row = sk_OPENSSL_PSTRING_value(db->data, 0);
  EXPECT_EQ(strlen(row[0]), 1000u);
  EXPECT_STREQ(row[1], "short");
}

// Test line without newline at end (should not be included)
TEST_F(TxtDbTest, LineWithoutNewline) {
  const char *data = "field1\tfield2";  // No newline at end
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);
  // The line without newline should not be parsed as a complete row
  EXPECT_EQ(sk_OPENSSL_PSTRING_num(db->data), 0u);
}

// Test error codes are properly set
TEST_F(TxtDbTest, ErrorCodes) {
  const char *data = "key1\tvalue1\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(data, strlen(data)));
  ASSERT_TRUE(bio);

  auto db = TXT_DB_read(bio, 2);
  ASSERT_TRUE(db);

  // Initially error should be OK (or uninitialized)
  // After a successful operation
  ASSERT_TRUE(TXT_DB_create_index(db, 0, nullptr, string_hash, string_cmp));
  
  const char *search_key = "key1";
  OPENSSL_STRING search_row[2] = {const_cast<char *>(search_key), nullptr};
  
  TXT_DB_get_by_index(db, 0, search_row);
  EXPECT_EQ(db->error, DB_ERROR_OK);

  // After an out of range error
  TXT_DB_get_by_index(db, 99, search_row);
  EXPECT_EQ(db->error, DB_ERROR_INDEX_OUT_OF_RANGE);
}
