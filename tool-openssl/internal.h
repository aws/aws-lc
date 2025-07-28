// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef TOOL_OPENSSL_INTERNAL_H
#define TOOL_OPENSSL_INTERNAL_H

#include <openssl/digest.h>
#include <memory>
#include <algorithm>
#include <string>
#include <utility>
#include <vector>
#include "../tool/internal.h"
#if !defined(O_BINARY)
#define O_BINARY 0
#endif

typedef bool (*tool_func_t)(const std::vector<std::string> &args);

struct Tool {
  const char *name;
  tool_func_t func;
};

bool IsNumeric(const std::string &str);

X509* CreateAndSignX509Certificate();
X509_CRL* createTestCRL();
bool isStringUpperCaseEqual(const std::string &a, const std::string &b);

bool LoadPrivateKeyAndSignCertificate(X509 *x509,
                                      const std::string &signkey_path);
EVP_PKEY* CreateTestKey(int key_bits);

tool_func_t FindTool(const std::string &name);
tool_func_t FindTool(int argc, char **argv, int &starting_arg);

bool CRLTool(const args_list_t &args);
bool dgstTool(const args_list_t &args);
bool md5Tool(const args_list_t &args);
bool pkcs8Tool(const args_list_t &args);
bool pkeyTool(const args_list_t &args);
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
typedef struct hash_entry_st {      // Represents a single certificate/CRL file
  struct hash_entry_st *next;       // Links to next entry in same bucket
  char *filename;                   // Actual filename
  uint8_t digest[EVP_MAX_MD_SIZE];  // File's cryptographic digest
} HASH_ENTRY;

typedef struct bucket_st {  // Groups entries with same hash
  struct bucket_st *next;   // Links to next bucket in hash table slot
  HASH_ENTRY *first_entry;  // Start of entry list
  HASH_ENTRY *last_entry;   // End of entry list
  uint32_t hash;            // Hash value of the certificates/CRLs
  uint16_t type;            // CERT or CRL Bucket
  uint16_t num_entries;     // Count of entries
} BUCKET;

enum Type { TYPE_CERT = 0, TYPE_CRL = 1 };
void add_entry(enum Type type, uint32_t hash, const char *filename,
               const uint8_t *digest);
BUCKET **get_table();
void cleanup_hash_table();

// Ordered argument processing (specific to tool-openssl)
namespace ordered_args {
typedef std::vector<std::pair<std::string, std::string>> ordered_args_map_t;

// Helper function to find an argument in the ordered args vector
static inline bool HasArgument(const ordered_args_map_t &args,
                               const std::string &arg_name) {
  return std::find_if(
             args.begin(), args.end(),
             [&arg_name](const std::pair<std::string, std::string> &pair) {
               return pair.first == arg_name;
             }) != args.end();
}

// Helper function to count occurrences of an argument
static inline size_t CountArgument(const ordered_args_map_t &args,
                                   const std::string &arg_name) {
  size_t count = 0;
  for (const auto &pair : args) {
    if (pair.first == arg_name) {
      count++;
    }
  }
  return count;
}

// Helper function to find an argument in the ordered args vector
static inline ordered_args_map_t::const_iterator FindArg(
    const ordered_args_map_t &args, const std::string &arg_name) {
  return std::find_if(
      args.begin(), args.end(),
      [&arg_name](const std::pair<std::string, std::string> &pair) {
        return pair.first == arg_name;
      });
}

// Parse arguments in order of appearance
bool ParseOrderedKeyValueArguments(ordered_args_map_t &out_args,
                                   args_list_t &extra_args,
                                   const args_list_t &args,
                                   const argument_t *templates);

// Get helpers for ordered arguments
bool GetUnsigned(unsigned *out, const std::string &arg_name,
                 unsigned default_value, const ordered_args_map_t &args);
bool GetString(std::string *out, const std::string &arg_name,
               std::string default_value, const ordered_args_map_t &args);
bool GetBoolArgument(bool *out, const std::string &arg_name,
                     const ordered_args_map_t &args);
}  // namespace ordered_args

#endif  // TOOL_OPENSSL_INTERNAL_H
