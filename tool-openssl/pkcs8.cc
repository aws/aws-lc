// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// PKCS8 Tool
// ----------
// 
// Implements PKCS8 key format operations with:
// - Cipher and PRF algorithm validation against allowlists
// - Format conversion between traditional and PKCS8
// - Secure key handling

#include <openssl/base.h>
#include <openssl/evp.h>
#include <openssl/pkcs8.h>
#include <openssl/rand.h>
#include <openssl/x509.h>
#include <openssl/pem.h>
#include <unordered_set>
#include <functional>
#include <cassert>
#include <cstring>
#include "internal.h"  // Includes openssl/bio.h, openssl/err.h, openssl/pem.h, etc.

// Maximum file size for cryptographic operations (1MB)
// Prevents DoS attacks through large file processing
static const long DEFAULT_MAX_CRYPTO_FILE_SIZE = 1024 * 1024;

// Maximum length for passwords (4KB)
// Provides reasonable bound while allowing complex passwords
static const size_t DEFAULT_MAX_SENSITIVE_STRING_LENGTH = 4096;

// Parameters for BIO validation with security-focused defaults
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

// Zero sensitive data from memory using volatile to prevent optimization
static void secure_clear_string(std::string& str) {
    if (!str.empty()) {
        volatile char* p = const_cast<volatile char*>(str.data());
        OPENSSL_cleanse(const_cast<char*>(p), str.size());
        str.clear();
    }
}

// SECURITY: Validate BIO size to prevent DoS from extremely large files
static bool validate_bio_size(BIO* bio, const BIOValidationParams& params = BIOValidationParams()) {
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

// Add error context to BIO operations
static bool write_key_bio(BIO* bio, EVP_PKEY* pkey, const std::string& format) {
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
static bool extract_password(const std::string& source, std::string* out_password) {
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

// SECURITY: Define allowlists of supported ciphers and PRF algorithms
static const std::unordered_set<std::string> kSupportedCiphers = {
    "aes-128-cbc", "aes-192-cbc", "aes-256-cbc", 
    "des-ede3-cbc", // Triple DES
    "des-cbc",      // Single DES (not recommended for security-sensitive applications)
    "rc2-cbc"       // RC2 (legacy)
};

static const std::unordered_set<std::string> kSupportedPRFs = {
    "hmacWithSHA1"  // Currently the only supported PRF in AWS-LC
};

// SECURITY: Validates cipher algorithm against security allowlist
static bool validate_cipher(const std::string& cipher_name) {
    if (kSupportedCiphers.find(cipher_name) == kSupportedCiphers.end()) {
        fprintf(stderr, "Error: Unsupported cipher algorithm: %s\n", cipher_name.c_str());
        fprintf(stderr, "Supported ciphers are:\n");
        for (const auto& cipher : kSupportedCiphers) {
            fprintf(stderr, "  %s\n", cipher.c_str());
        }
        return false;
    }
    return true;
}

// SECURITY: Validates PRF algorithm against security allowlist
static bool validate_prf(const std::string& prf_name) {
    if (kSupportedPRFs.find(prf_name) == kSupportedPRFs.end()) {
        fprintf(stderr, "Error: Unsupported PRF algorithm: %s\n", prf_name.c_str());
        fprintf(stderr, "AWS-LC only supports the following PRF algorithms:\n");
        for (const auto& prf : kSupportedPRFs) {
            fprintf(stderr, "  %s\n", prf.c_str());
        }
        return false;
    }
    return true;
}

// SECURITY: Helper function for consistent error handling and password cleanup
static bool cleanup_and_fail(std::string& passin, 
                          std::string& passout,
                          const char* error_msg) {
    assert(error_msg != nullptr);
    fprintf(stderr, "Error: %s\n", error_msg);
    secure_clear_string(passin);
    secure_clear_string(passout);
    return false;
}

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-in", kOptionalArgument, "Input file" },
  { "-out", kOptionalArgument, "Output file" },
  { "-inform", kOptionalArgument, "Input format (DER or PEM)" },
  { "-outform", kOptionalArgument, "Output format (DER or PEM)" },
  { "-topk8", kBooleanArgument, "Convert traditional format to PKCS#8" },
  { "-nocrypt", kBooleanArgument, "Use unencrypted private key" },
  { "-v2", kOptionalArgument, "Use PKCS#5 v2.0 and specified cipher" },
  { "-v2prf", kOptionalArgument, "Use specified PRF algorithm with PKCS#5 v2.0" },
  { "-passin", kOptionalArgument, "Input file passphrase source" },
  { "-passout", kOptionalArgument, "Output file passphrase source" },
  { "", kOptionalArgument, "" }  // Terminator entry - must be the last one
};

// Helper function to print OpenSSL errors
static void print_errors() {
  ERR_print_errors_fp(stderr);
}

// SECURITY: Helper function to read a private key in any format with validation
static bssl::UniquePtr<EVP_PKEY> read_private_key(BIO* in_bio, const char* passin, const std::string& format) {
  if (!in_bio) {
    fprintf(stderr, "Error: Null BIO handle in read_private_key\n");
    return nullptr;
  }
  
  bssl::UniquePtr<EVP_PKEY> pkey;

  // Handle DER format input
  if (format == "DER") {
    // For DER format, first try as unencrypted PKCS8
    BIO_reset(in_bio);
    bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(d2i_PKCS8_PRIV_KEY_INFO_bio(in_bio, nullptr));
    
    if (p8inf) {
      pkey.reset(EVP_PKCS82PKEY(p8inf.get()));
      if (pkey) {
        return pkey;
      }
    }
    
    // If that failed and a password is provided, try as encrypted PKCS8
    if (passin) {
      BIO_reset(in_bio);
      pkey.reset(d2i_PKCS8PrivateKey_bio(in_bio, nullptr, nullptr, const_cast<char*>(passin)));
      if (pkey) {
        return pkey;
      }
    }
    
    // Finally try as traditional format DER
    BIO_reset(in_bio);
    pkey.reset(d2i_PrivateKey_bio(in_bio, nullptr));
    if (pkey) {
      return pkey;
    }
    
    // All DER attempts failed
    return nullptr;
  }
  
  // For PEM format input (default)
  BIO_reset(in_bio);
  pkey.reset(PEM_read_bio_PrivateKey(in_bio, nullptr, nullptr, const_cast<char*>(passin)));
  if (pkey) {
    return pkey;
  }

  // If we get here, all attempts failed
  return nullptr;
}

bool pkcs8Tool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  bool help = false;
  GetBoolArgument(&help, "-help", parsed_args);
  if (help) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in_path, out_path;
  std::string v2_cipher, v2_prf;
  std::string passin_arg, passout_arg;
  bool topk8 = false, nocrypt = false;

  GetString(&in_path, "-in", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetBoolArgument(&topk8, "-topk8", parsed_args);
  GetBoolArgument(&nocrypt, "-nocrypt", parsed_args);
  GetString(&v2_cipher, "-v2", "", parsed_args);
  GetString(&v2_prf, "-v2prf", "", parsed_args);
  GetString(&passin_arg, "-passin", "", parsed_args);
  GetString(&passout_arg, "-passout", "", parsed_args);
  
  // Handle format options
  std::string inform, outform;
  GetString(&inform, "-inform", "PEM", parsed_args);
  GetString(&outform, "-outform", "PEM", parsed_args);
  
  // SECURITY: Validate formats
  if (inform != "PEM" && inform != "DER") {
    fprintf(stderr, "Error: '-inform' option must specify a valid encoding DER|PEM\n");
    return false;
  }
  
  if (outform != "PEM" && outform != "DER") {
    fprintf(stderr, "Error: '-outform' option must specify a valid encoding DER|PEM\n");
    return false;
  }

  if (in_path.empty()) {
    fprintf(stderr, "Error: missing required argument '-in'\n");
    return false;
  }

  // Create input BIO with validation
  bssl::UniquePtr<BIO> in_bio(BIO_new_file(in_path.c_str(), "rb"));
  if (!in_bio) {
    fprintf(stderr, "Error: Could not open file: %s\n", in_path.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }

  // Validate file size to prevent DoS attacks
  if (!validate_bio_size(in_bio.get())) {
    fprintf(stderr, "Error: File size validation failed for: %s\n", in_path.c_str());
    return false;
  }

  // Create output BIO
  bssl::UniquePtr<BIO> out_bio;
  if (out_path.empty()) {
    out_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    out_bio.reset(BIO_new_file(out_path.c_str(), "wb"));
  }
  
  if (!out_bio) {
    fprintf(stderr, "Error: Could not open file for writing\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  // SECURITY: Extract password with validation
  std::string passin_password, passout_password;
  const char* passin = nullptr;
  const char* passout = nullptr;

  if (!passin_arg.empty()) {
    if (!extract_password(passin_arg, &passin_password)) {
      return false;  // Error message already printed
    }
    passin = passin_password.c_str();
  }

  if (!passout_arg.empty()) {
    if (!extract_password(passout_arg, &passout_password)) {
      secure_clear_string(passin_password); // Clean up passin if passout fails
      return false;  // Error message already printed
    }
    passout = passout_password.c_str();
  }

  // SECURITY: Validate cipher and PRF if specified
  if (!v2_cipher.empty() && !validate_cipher(v2_cipher)) {
    return cleanup_and_fail(passin_password, passout_password, "Invalid cipher specified");
  }

  if (!v2_prf.empty() && !validate_prf(v2_prf)) {
    return cleanup_and_fail(passin_password, passout_password, "Invalid PRF algorithm specified");
  }

  // Read the private key using the improved method with format
  bssl::UniquePtr<EVP_PKEY> pkey = read_private_key(in_bio.get(), passin, inform);
  if (!pkey) {
    return cleanup_and_fail(passin_password, passout_password, 
                          "Failed to read private key. Check that the file contains a valid key and the password (if any) is correct");
  }

  bool result = false;

  if (topk8) {
    bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(EVP_PKEY2PKCS8(pkey.get()));
    if (!p8inf) {
      print_errors();
      return cleanup_and_fail(passin_password, passout_password, "Failed to convert key to PKCS#8 format");
    }

    if (nocrypt) {
      // Handle output format using helper function for unencrypted PKCS8
      ERR_clear_error();
      if (outform == "PEM") {
        result = PEM_write_bio_PKCS8_PRIV_KEY_INFO(out_bio.get(), p8inf.get());
      } else { // DER
        result = i2d_PKCS8_PRIV_KEY_INFO_bio(out_bio.get(), p8inf.get());
      }
      
      if (!result) {
        BIOError error = BIOError::from_current_error();
        error.type = BIOErrorType::KEY_OPERATION_ERROR;
        error.message = "Failed to write PKCS8 private key info in " + outform + " format";
        handle_bio_error(error);
      }
    } else {
      // When -topk8 is used without -nocrypt, we're encrypting the key
      const EVP_CIPHER *cipher = nullptr;
      
      // If -v2 is specified, it must have a value
      if (parsed_args.count("-v2") > 0) {
        if (v2_cipher.empty()) {
          return cleanup_and_fail(passin_password, passout_password, 
                                "-v2 option requires a cipher name argument");
        }
        
        // SECURITY: Already validated the cipher above
        cipher = EVP_get_cipherbyname(v2_cipher.c_str());
        if (!cipher) {
          // Should not happen if validation passed, but handle as a fallback
          return cleanup_and_fail(passin_password, passout_password, 
                                "Failed to initialize cipher");
        }
      } else {
        // If -topk8 is used without -nocrypt and without explicit -v2,
        // we still use PKCS#5 v2.0 with the default cipher
        cipher = EVP_aes_256_cbc();
      }

      if (!v2_prf.empty()) {
        // SECURITY: PRF already validated above
        int pbe_nid = OBJ_txt2nid(v2_prf.c_str());
        if (pbe_nid == NID_undef) {
          return cleanup_and_fail(passin_password, passout_password, 
                                "Unknown PRF algorithm");
        }
        // This check is kept for compatibility with existing code
        if (pbe_nid != NID_hmacWithSHA1) {
          return cleanup_and_fail(passin_password, passout_password,
                                "AWS-LC only supports hmacWithSHA1 as the PRF algorithm");
        }
      }

      if (!passout) {
        return cleanup_and_fail(passin_password, passout_password, 
                              "-passout must be provided for encryption");
      }

      // Handle encrypted output for different formats
      if (outform == "PEM") {
        result = PEM_write_bio_PKCS8PrivateKey(out_bio.get(), pkey.get(), 
                                             cipher, passout, strlen(passout),
                                             nullptr, nullptr);
      } else { // DER
        result = i2d_PKCS8PrivateKey_bio(out_bio.get(), pkey.get(),
                                        cipher, passout, strlen(passout),
                                        nullptr, nullptr);
      }
    }
  } else {
    // Use the write_key_bio utility for traditional key format
    result = write_key_bio(out_bio.get(), pkey.get(), outform);
  }

  if (!result) {
    print_errors();
    return cleanup_and_fail(passin_password, passout_password, "Failed to write private key");
  }

  // Ensure data is flushed to disk
  BIO_flush(out_bio.get());

  // SECURITY: Clear passwords before returning
  secure_clear_string(passin_password);
  secure_clear_string(passout_password);
  return true;
}
