// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef TOOL_OPENSSL_INTERNAL_H
#define TOOL_OPENSSL_INTERNAL_H

#include <openssl/digest.h>
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


X509_CRL *createTestCRL();
bool isStringUpperCaseEqual(const std::string &a, const std::string &b);

// Password extracting utility for -passin and -passout options
namespace pass_util {
// Password source types for handling different input methods
enum class Source : uint8_t {
  kNone,   // Empty or invalid source
  kPass,   // Direct password with pass: prefix
  kFile,   // Password from file with file: prefix
  kEnv,    // Password from environment with env: prefix
  kStdin,  // Password from stdin
#ifndef _WIN32
  kFd,  // Password from file descriptor with fd: prefix (Unix only)
#endif
};

// Custom deleter for sensitive strings that securely clears memory before
// deletion. This ensures passwords are securely removed from memory when no
// longer needed, preventing potential exposure in memory dumps or swap files.
void SensitiveStringDeleter(std::string *str);

// Extracts password from a source string, modifying it in place if successful.
// source: Password source string in one of the following formats:
//   - pass:password (direct password, e.g., "pass:mypassword")
//   - file:/path/to/file (password from file)
//   - env:VAR_NAME (password from environment variable)
//   - stdin (password from standard input)
//   - fd:N (password from file descriptor N, Unix only)
// The source string will be replaced with the extracted password if successful.
// Returns bool indicating success or failure:
//   - true: Password was successfully extracted and stored in source
//   - false: Error occurred, error message printed to stderr
// Error cases:
//   - Invalid format string (missing or unknown prefix)
//   - File access errors (file not found, permission denied)
//   - Environment variable not set
//   - Memory allocation failures
bool ExtractPassword(bssl::UniquePtr<std::string> &source);

// Same process as ExtractPassword but used for -passin and -passout within same
// tool. Special handling:
// - If same file is used for both passwords, reads first line for passin
//   and second line for passout in a single file operation matching OpenSSL
//   behavior
// - If stdin is used for both passwords, reads first line for passin
//   and second line for passout from standard input matching OpenSSL behavior
bool ExtractPasswords(bssl::UniquePtr<std::string> &passin,
                      bssl::UniquePtr<std::string> &passout);

}  // namespace pass_util

// Custom deleter used for -passin -passout options
BSSL_NAMESPACE_BEGIN
BORINGSSL_MAKE_DELETER(std::string, pass_util::SensitiveStringDeleter)
BSSL_NAMESPACE_END

EVP_PKEY *CreateTestKey(int key_bits);

tool_func_t FindTool(const std::string &name);
tool_func_t FindTool(int argc, char **argv, int &starting_arg);

bool CRLTool(const args_list_t &args);
bool dgstTool(const args_list_t &args);
bool dhparamTool(const args_list_t &args);
bool ecTool(const args_list_t &args);
bool ecparamTool(const args_list_t &args);
bool encTool(const args_list_t &args);
bool genrsaTool(const args_list_t &args);
bool md5Tool(const args_list_t &args);
bool pkcs8Tool(const args_list_t &args);
bool pkeyTool(const args_list_t &args);
bool pkeyutlTool(const args_list_t &args);
bool RehashTool(const args_list_t &args);
bool reqTool(const args_list_t &args);
bool rsaTool(const args_list_t &args);
bool sha1Tool(const args_list_t &args);
bool SClientTool(const args_list_t &args);
bool VerifyTool(const args_list_t &args);
bool VersionTool(const args_list_t &args);
bool X509Tool(const args_list_t &args);

// Req Tool Utilities
bssl::UniquePtr<X509_NAME> ParseSubjectName(std::string &subject_string);


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

static inline void FindAll(std::vector<std::string> &result,
                           const std::string &arg_name,
                           const ordered_args_map_t &args) {
  for (const auto &pair : args) {
    if (pair.first == arg_name) {
      result.push_back(pair.second);
    }
  }
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

bool GetExclusiveBoolArgument(std::string *out_arg, const argument_t *templates,
                              std::string default_out_arg,
                              const ordered_args_map_t &args);
}  // namespace ordered_args

void SetUmaskForPrivateKey();

#endif  // TOOL_OPENSSL_INTERNAL_H
