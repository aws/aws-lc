// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef INTERNAL_H
#define INTERNAL_H

#include "../tool/internal.h"
#include <openssl/digest.h>
#include <string>
#include <vector>

#if !defined(O_BINARY)
#define O_BINARY 0
#endif

typedef bool (*tool_func_t)(const std::vector<std::string> &args);

struct Tool {
  const char *name;
  tool_func_t func;
};

bool IsNumeric(const std::string& str);

X509* CreateAndSignX509Certificate();
X509_CRL* createTestCRL();

bool LoadPrivateKeyAndSignCertificate(X509 *x509, const std::string &signkey_path);

tool_func_t FindTool(const std::string &name);
tool_func_t FindTool(int argc, char **argv, int &starting_arg);

bool CRLTool(const args_list_t &args);
bool dgstTool(const args_list_t &args);
bool md5Tool(const args_list_t &args);
bool RehashTool(const args_list_t &args);
bool reqTool(const args_list_t &args);
bool rsaTool(const args_list_t &args);
bool SClientTool(const args_list_t &args);
bool VerifyTool(const args_list_t &args);
bool VersionTool(const args_list_t &args);
bool X509Tool(const args_list_t &args);

// Req Tool Utilities
bssl::UniquePtr<X509_NAME> parse_subject_name(std::string &subject_string);


// Rehash tool Utils
typedef struct hash_entry_st {        // Represents a single certificate/CRL file
  struct hash_entry_st *next;         // Links to next entry in same bucket
  char *filename;                     // Actual filename
  uint8_t digest[EVP_MAX_MD_SIZE];    // File's cryptographic digest
} HASH_ENTRY;

typedef struct bucket_st {    // Groups entries with same hash
  struct bucket_st *next;     // Links to next bucket in hash table slot
  HASH_ENTRY *first_entry;    // Start of entry list
  HASH_ENTRY *last_entry;     // End of entry list
  uint32_t hash;              // Hash value of the certificates/CRLs
  uint16_t type;              // CERT or CRL Bucket
  uint16_t num_entries;       // Count of entries
} BUCKET;

enum Type {
  TYPE_CERT=0, TYPE_CRL=1
};
void add_entry(enum Type type, uint32_t hash, const char *filename,
                     const uint8_t *digest);
BUCKET** get_table();
void cleanup_hash_table();

#endif //INTERNAL_H
