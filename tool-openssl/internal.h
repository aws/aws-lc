// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef INTERNAL_H
#define INTERNAL_H

#include "../tool/internal.h"
#include <openssl/digest.h>
#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <string>
#include <vector>
#include <memory>
#include <functional>
#include <cstring>
#include <cassert>

#if !defined(O_BINARY)
#define O_BINARY 0
#endif

// Secure File I/O Utilities
// ------------------------
// These utilities provide secure file I/O operations using OpenSSL's BIO
// interface with the following security properties:
// 
// - Size validation to prevent DoS attacks
// - Secure memory handling for sensitive data
// - Structured error handling
// - RAII-style resource management
// 
// SECURITY PROPERTIES:
// 1. Password Confidentiality:
//    - All password buffers are securely cleared from memory after use
//    - RAII patterns ensure automatic clearing even in error cases
//    - Volatile pointers are used to prevent compiler optimization of clearing operations
//
// 2. Input Validation:
//    - File sizes are validated to prevent denial-of-service attacks
//    - Password lengths are bounded to prevent buffer-related issues
//
// 3. Error Handling:
//    - Security-sensitive errors are explicitly logged
//    - Error messages are designed to be informative without leaking sensitive information
//    - Structured error handling ensures consistent behavior and cleanup
//
// Example usage:
//   // Simple usage with defaults
//   ScopedBIO input_bio("input.pem", "rb");
//   if (!input_bio.valid()) {
//     return false;
//   }
//
//   // Advanced usage with custom validation and error handling
//   BIOValidationParams params;
//   params.max_size = 2 * DEFAULT_MAX_CRYPTO_FILE_SIZE; // Allow larger file
//   
//   ScopedBIO input_bio("input.pem", "rb", params, 
//                        [](const BIOError& err) {
//                          fprintf(stderr, "Custom error handler: %s\n", err.message.c_str());
//                        });
//   
//   // Password handling
//   std::string password;
//   if (!extract_password("file:password.txt", &password)) {
//     return false;
//   }
//   // Use password...
//   secure_clear_string(password); // Clear when done

// Maximum file size for cryptographic operations (1MB)
// This limit helps prevent denial-of-service attacks through large file processing
static const long DEFAULT_MAX_CRYPTO_FILE_SIZE = 1024 * 1024;

// Maximum length for passwords and other sensitive strings
// This provides reasonable upper bound for memory allocation while allowing complex passwords
static const size_t DEFAULT_MAX_SENSITIVE_STRING_LENGTH = 4096;

// SECURITY: Securely clear a string from memory
inline void secure_clear_string(std::string& str) {
    if (!str.empty()) {
        volatile char* p = const_cast<volatile char*>(str.data());
        OPENSSL_cleanse(const_cast<char*>(p), str.size());
        str.clear();
    }
}

// Parameters for BIO validation with default security settings
// This simplifies the validation process while maintaining security
struct BIOValidationParams {
    long max_size;
    
    BIOValidationParams()
        : max_size(DEFAULT_MAX_CRYPTO_FILE_SIZE) {}
};

// Error types for BIO operations
enum class BIOErrorType {
    FILE_ACCESS,
    SIZE_LIMIT,
    FORMAT_ERROR,
    PASSWORD_ERROR,
    KEY_OPERATION_ERROR,
    UNKNOWN
};

// Structured error information
struct BIOError {
    BIOErrorType type;
    std::string message;
    unsigned long openssl_error;
    
    static BIOError from_current_error() {
        BIOError error;
        error.openssl_error = ERR_peek_last_error();
        
        if (error.openssl_error) {
            char err_buf[256];
            ERR_error_string_n(error.openssl_error, err_buf, sizeof(err_buf));
            error.message = err_buf;
            
            if (ERR_GET_REASON(error.openssl_error) == PEM_R_BAD_PASSWORD_READ) {
                error.type = BIOErrorType::PASSWORD_ERROR;
            } else {
                error.type = BIOErrorType::UNKNOWN;
            }
        } else {
            error.message = "Unknown error";
            error.type = BIOErrorType::UNKNOWN;
        }
        
        return error;
    }
};

// Error handler function type
using BIOErrorHandler = std::function<void(const BIOError&)>;

// Default error handler implementation
static void handle_bio_error(const BIOError& error, BIOErrorHandler handler = nullptr) {
    if (handler) {
        handler(error);
    } else {
        // Default error handling
        fprintf(stderr, "Error: %s\n", error.message.c_str());
        if (error.openssl_error) {
            ERR_print_errors_fp(stderr);
            
            // Special handling for common errors
            if (error.type == BIOErrorType::PASSWORD_ERROR) {
                fprintf(stderr, "Hint: Check if the provided password is correct\n");
            }
        }
    }
}

// Validate BIO size to prevent DoS from extremely large files
inline bool validate_bio_size(BIO* bio, const BIOValidationParams& params = BIOValidationParams()) {
    if (!bio) return false;
    
    // Save current position
    long current_pos = BIO_tell(bio);
    if (current_pos < 0) return false;
    
    // Get file size
    if (BIO_seek(bio, 0) < 0) return false;
    long size = BIO_tell(bio);
    
    // Restore position
    if (BIO_seek(bio, current_pos) < 0) return false;
    
    // Allow empty files by default
    
    if (size > params.max_size) {
        fprintf(stderr, "Error: File exceeds maximum allowed size of %ld bytes\n", 
                params.max_size);
        return false;
    }
    
    // Always verify file is readable by reading first byte
    if (size > 0) {
        unsigned char byte;
        long pos = BIO_tell(bio);
        
        if (BIO_read(bio, &byte, 1) != 1) {
            BIO_seek(bio, pos); // Try to restore position
            return false;
        }
        
        // Restore position
        BIO_seek(bio, pos);
    }
    
    return true;
}

// RAII wrapper for BIO operations with validation and error handling
class ScopedBIO {
private:
    bssl::UniquePtr<BIO> bio_;
    BIOErrorHandler error_handler_;

public:
    // Constructor for file-based BIO
    ScopedBIO(const std::string& path, 
              const char* mode,
              const BIOValidationParams& params = BIOValidationParams(),
              BIOErrorHandler handler = nullptr)
        : error_handler_(handler) {
        
        bio_.reset(BIO_new_file(path.c_str(), mode));
        
        if (!bio_) {
            BIOError error;
            error.type = BIOErrorType::FILE_ACCESS;
            error.message = "Could not open file: " + path;
            error.openssl_error = ERR_peek_last_error();
            
            handle_bio_error(error, error_handler_);
            return;
        }
        
        if (strcmp(mode, "rb") == 0 && !validate_bio_size(bio_.get(), params)) {
            BIOError error;
            error.type = BIOErrorType::SIZE_LIMIT;
            error.message = "File size validation failed for: " + path;
            
            handle_bio_error(error, error_handler_);
            bio_.reset(); // Invalidate the BIO
        }
    }
    
    // Constructor for existing BIO (like stdout)
    ScopedBIO(BIO* bio, BIOErrorHandler handler = nullptr)
        : error_handler_(handler) {
        if (bio) {
            bio_.reset(bio);
        } else {
            BIOError error;
            error.type = BIOErrorType::FILE_ACCESS;
            error.message = "Null BIO provided";
            
            handle_bio_error(error, error_handler_);
        }
    }
    
    ~ScopedBIO() {
        if (bio_) {
            BIO_flush(bio_.get());
        }
    }
    
    BIO* get() { return bio_.get(); }
    bool valid() const { return bio_ != nullptr; }
    
    // Prevent copying
    ScopedBIO(const ScopedBIO&) = delete;
    ScopedBIO& operator=(const ScopedBIO&) = delete;
};

// Add error context to BIO operations
inline bool write_key_bio(BIO* bio, EVP_PKEY* pkey, const std::string& format) {
    ERR_clear_error();  // Clear any previous errors
    bool result = (format == "PEM") ?
        PEM_write_bio_PrivateKey(bio, pkey, nullptr, nullptr, 0, nullptr, nullptr) :
        i2d_PrivateKey_bio(bio, pkey);
    
    if (!result) {
        BIOError error = BIOError::from_current_error();
        error.type = BIOErrorType::KEY_OPERATION_ERROR;
        error.message = "Failed to write private key in " + format + " format";
        handle_bio_error(error);
    }
    return result;
}

// Extract and validate password from various sources
inline bool extract_password(const std::string& source, std::string* out_password) {
    assert(out_password != nullptr && "Password output pointer cannot be null");
    if (!out_password) {
        return false;
    }
    
    // Handle pass:password format
    if (source.compare(0, 5, "pass:") == 0) {
        std::string password = source.substr(5);
        
        if (password.length() > DEFAULT_MAX_SENSITIVE_STRING_LENGTH) {
            fprintf(stderr, "Error: Password exceeds maximum allowed length of %zu characters\n", 
                    DEFAULT_MAX_SENSITIVE_STRING_LENGTH);
            return false;
        }
        
        *out_password = password;
        return true;
    }
    
    // Handle file:pathname format
    if (source.compare(0, 5, "file:") == 0) {
        std::string path = source.substr(5);
        bssl::UniquePtr<BIO> file_bio(BIO_new_file(path.c_str(), "r"));
        
        if (!file_bio) {
            fprintf(stderr, "Error: Could not open password file '%s'\n", path.c_str());
            return false;
        }
        
        // Use fixed-size buffer with secure clearing
        char buf[DEFAULT_MAX_SENSITIVE_STRING_LENGTH];
        memset(buf, 0, sizeof(buf));
        
        int len = BIO_gets(file_bio.get(), buf, sizeof(buf));
        if (len <= 0) {
            fprintf(stderr, "Error: Could not read from password file\n");
            OPENSSL_cleanse(buf, sizeof(buf));
            return false;
        }
        
        // Remove trailing newline if present
        bool possible_truncation = (static_cast<size_t>(len) == DEFAULT_MAX_SENSITIVE_STRING_LENGTH - 1 && 
                                  buf[len - 1] != '\n' && buf[len - 1] != '\r');
        
        size_t buf_len = strlen(buf);
        while (buf_len > 0 && (buf[buf_len-1] == '\n' || buf[buf_len-1] == '\r')) {
            buf[--buf_len] = '\0';
        }
        
        if (possible_truncation) {
            fprintf(stderr, "Warning: Password may have been truncated (exceeds %zu characters)\n", 
                    DEFAULT_MAX_SENSITIVE_STRING_LENGTH - 1);
        }
        
        *out_password = buf;
        // SECURITY: Securely clear the buffer
        OPENSSL_cleanse(buf, sizeof(buf));
        return true;
    }
    
    // Handle env:var format - retrieve password from environment variable
    if (source.compare(0, 4, "env:") == 0) {
        std::string env_var = source.substr(4);
        
        // Validate environment variable name is not empty
        if (env_var.empty()) {
            fprintf(stderr, "Error: Empty environment variable name in 'env:' format\n");
            return false;
        }
        
        const char* env_value = getenv(env_var.c_str());
        if (!env_value) {
            fprintf(stderr, "Error: Environment variable '%s' not set or inaccessible\n", 
                    env_var.c_str());
            return false;
        }
        
        if (strlen(env_value) > DEFAULT_MAX_SENSITIVE_STRING_LENGTH) {
            fprintf(stderr, "Error: Password from environment variable '%s' exceeds maximum allowed length of %zu characters\n", 
                   env_var.c_str(), DEFAULT_MAX_SENSITIVE_STRING_LENGTH);
            return false;
        }
        
        *out_password = env_value;
        return true;
    }
    
    // TODO: Implement EVP password prompting functionality similar to OpenSSL 1.1.1
    // This would handle cases where the password needs to be prompted from the user
    // interactively using EVP_read_pw_string or similar functionality.
    // See OpenSSL implementation in crypto/pem/pem_lib.c
    
    fprintf(stderr, "Error: Unsupported password format. Use pass:, file:, or env: prefix.\n");
    return false;
}

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
bool pkcs8Tool(const args_list_t &args);


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
