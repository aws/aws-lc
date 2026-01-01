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

// Format enum for PEM and DER output/input formats
enum Format {
  FORMAT_PEM = 1,
  FORMAT_DER = 2,
  FORMAT_UNKNOWN = 3
};

typedef bool (*tool_func_t)(const std::vector<std::string> &args);

struct Tool {
  const char *name;
  tool_func_t func;
};

bool IsNumeric(const std::string &str);


X509_CRL *createTestCRL();
bool isStringUpperCaseEqual(const std::string &a, const std::string &b);

// Password class that wraps std::string with secure memory clearing
class Password {
private:
    std::string data_;
    
    // Helper method to securely clear current data
    void secure_clear() {
        if (!data_.empty()) {
            OPENSSL_cleanse(&data_[0], data_.size());
        }
    }

public:
    // Default constructor
    Password() = default;
    
    // String constructor
    explicit Password(const std::string& str) : data_(str) {}
    explicit Password(std::string&& str) : data_(std::move(str)) {}
    
    // Copy constructor and assignment
    Password(const Password& other) : data_(other.data_) {}
    Password& operator=(const Password& other) {
        if (this != &other) {
            secure_clear();
            data_ = other.data_;
        }
        return *this;
    }
    
    // Move constructor and assignment
    Password(Password&& other) noexcept : data_(std::move(other.data_)) {}
    Password& operator=(Password&& other) noexcept {
        if (this != &other) {
            secure_clear();
            data_ = std::move(other.data_);
        }
        return *this;
    }
    
    // Destructor with secure clearing
    ~Password() {
        secure_clear();
    }
    
    // Access methods
    std::string& get() { return data_; }
    const std::string& get() const { return data_; }
    
    // Implicit conversion for ease of use
    operator std::string&() { return data_; }
    operator const std::string&() const { return data_; }
    
    // Common string operations
    bool empty() const { return data_.empty(); }
    size_t size() const { return data_.size(); }
    void clear() { 
        secure_clear();
        data_.clear(); 
    }
};

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
bool ExtractPassword(Password &source);

// Same process as ExtractPassword but used for -passin and -passout within same
// tool. Special handling:
// - If same file is used for both passwords, reads first line for passin
//   and second line for passout in a single file operation matching OpenSSL
//   behavior
// - If stdin is used for both passwords, reads first line for passin
//   and second line for passout from standard input matching OpenSSL behavior
bool ExtractPasswords(Password &passin, Password &passout);

}  // namespace pass_util

EVP_PKEY *CreateTestKey(int key_bits);

tool_func_t FindTool(const std::string &name);
tool_func_t FindTool(int argc, char **argv, int &starting_arg);

bool CRLTool(const args_list_t &args);
bool asn1parseTool(const args_list_t &args);
bool dgstTool(const args_list_t &args);
bool dhparamTool(const args_list_t &args);
bool ecTool(const args_list_t &args);
bool ecparamTool(const args_list_t &args);
bool encTool(const args_list_t &args);
bool genpkeyTool(const args_list_t &args);
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

// ApplyPkeyCtrlString parses the options in |pkeyopt| and passes them to
// |EVP_PKEY_CTX_ctrl_str|. It returns false if the parsing or memory allocation
// during string duplication was unsuccesful.
bool ApplyPkeyCtrlString(EVP_PKEY_CTX *ctx, const char *pkeyopt);

// WritePrivateKey writes the private key contents of |pkey| to |out| based on
// |format|. It returns false if the write was unsuccessful.
bool WritePrivateKey(EVP_PKEY *pkey, bssl::UniquePtr<BIO> &out, int format);

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
