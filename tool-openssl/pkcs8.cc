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
#include "internal.h"  

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

// Define PKCS8 reason codes for the CLI tool
#ifndef PKCS8_R_CLI_ERROR
#define PKCS8_R_CLI_ERROR 100
#endif

// Define all PKCS8 errors with X-Macro pattern
#define PKCS8_ERRORS(X) \
    X(FILE_TOO_LARGE,    "File exceeds maximum allowed size of %ld bytes",                               true, FILE) \
    X(CANNOT_OPEN_FILE,  "Could not open file: %s",                                                      true, FILE) \
    X(CANNOT_OPEN_WRITE, "Could not open file for writing",                                             false, FILE) \
    X(INVALID_FORMAT,    "'-%s' option must specify a valid encoding DER|PEM",                           true, FORMAT) \
    X(MISSING_ARGUMENT,  "missing required argument '-in'",                                              true, ARGUMENT) \
    X(PASSWORD_TOO_LONG, "Password exceeds maximum allowed length of %zu characters",                    true, PASSWORD) \
    X(CANNOT_OPEN_PWFILE,"Could not open password file '%s'",                                            true, PASSWORD) \
    X(CANNOT_READ_PWFILE,"Could not read from password file",                                           false, PASSWORD) \
    X(EMPTY_ENV_VAR,     "Empty environment variable name in 'env:' format",                            false, PASSWORD) \
    X(ENV_VAR_NOT_SET,   "Environment variable '%s' not set or inaccessible",                            true, PASSWORD) \
    X(ENV_VAR_TOO_LONG,  "Password from environment variable '%s' exceeds maximum allowed length of %zu characters", true, PASSWORD) \
    X(UNSUPPORTED_PWFMT, "Unsupported password format. Use pass:, file:, or env: prefix.",              false, PASSWORD) \
    X(UNSUPPORTED_CIPHER,"Unsupported cipher algorithm: %s",                                             true, CRYPTO) \
    X(UNSUPPORTED_PRF,   "Unsupported PRF algorithm: %s",                                                true, CRYPTO) \
    X(NULL_BIO_HANDLE,   "Null BIO handle in read_private_key",                                         false, INTERNAL) \
    X(FAILED_READ_KEY,   "Failed to read private key. Check that the file contains a valid key and the password (if any) is correct", false, CRYPTO) \
    X(FAILED_CONVERT,    "Failed to convert key to PKCS#8 format",                                      false, CRYPTO) \
    X(FAILED_WRITE_KEY,  "Failed to write PKCS8 private key info in %s format",                          true, CRYPTO) \
    X(FAILED_TRADITIONAL,"Failed to write private key in traditional format",                           false, CRYPTO) \
    X(FAILED_WRITE_PKCS8,"Failed to write unencrypted PKCS8 key",                                       false, CRYPTO) \
    X(FAILED_WRITE_ENC,  "Failed to write encrypted private key",                                       false, CRYPTO) \
    X(MISSING_PASSOUT,   "-passout must be provided for encryption",                                    false, PASSWORD) \
    X(V2_NO_CIPHER,      "-v2 option requires a cipher name argument",                                  false, ARGUMENT) \
    X(INIT_CIPHER_FAILED,"Failed to initialize cipher",                                                 false, CRYPTO) \
    X(UNKNOWN_PRF,       "Unknown PRF algorithm",                                                       false, CRYPTO) \
    X(INVALID_PRF,       "AWS-LC only supports hmacWithSHA1 as the PRF algorithm",                      false, CRYPTO)

// Define error categories
enum PKCS8_ERROR_CATEGORY {
    CATEGORY_GENERAL,
    CATEGORY_FILE,
    CATEGORY_FORMAT,
    CATEGORY_ARGUMENT,
    CATEGORY_PASSWORD,
    CATEGORY_CRYPTO,
    CATEGORY_INTERNAL
};

// Generate enum for error codes
enum PKCS8_ERROR_CODE {
#define X(name, msg, has_args, category) PKCS8_ERR_##name,
    PKCS8_ERRORS(X)
#undef X
    PKCS8_ERR_LAST_ERROR
};

// Generate message array
static const struct ErrorInfo {
    const char* format;
    bool has_args;
    PKCS8_ERROR_CATEGORY category;
} ERROR_MESSAGES[] = {
#define X(name, msg, has_args, category) {msg, has_args, CATEGORY_##category},
    PKCS8_ERRORS(X)
#undef X
};

// Ensure array and enum stay in sync
static_assert(sizeof(ERROR_MESSAGES)/sizeof(ERROR_MESSAGES[0]) == PKCS8_ERR_LAST_ERROR,
              "ERROR_MESSAGES array must match enum size");

// Helper function for reporting errors from the PKCS8 CLI tool
static bool report_error(PKCS8_ERROR_CODE code, ...) {
    // Log to OpenSSL error queue with PKCS8 library code
    OPENSSL_PUT_ERROR(PKCS8, PKCS8_R_CLI_ERROR);
    
    // Check bounds
    if (code < 0 || code >= PKCS8_ERR_LAST_ERROR || !ERROR_MESSAGES[code].format) {
        fprintf(stderr, "PKCS8 CLI Error: Internal error (invalid error code)\n");
        return false;
    }
    
    // Format the message if it has arguments
    if (ERROR_MESSAGES[code].has_args) {
        char buffer[512];
        va_list args;
        va_start(args, code);
        vsnprintf(buffer, sizeof(buffer), ERROR_MESSAGES[code].format, args);
        va_end(args);
        
        // Add detailed error data to OpenSSL error queue
        ERR_add_error_data(1, buffer);
        
        // Print user-friendly error to stderr
        fprintf(stderr, "PKCS8 CLI Error: %s\n", buffer);
    } else {
        // For messages without arguments, use format directly
        ERR_add_error_data(1, ERROR_MESSAGES[code].format);
        fprintf(stderr, "PKCS8 CLI Error: %s\n", ERROR_MESSAGES[code].format);
    }
    return false;
}

// Macro for reporting errors from the PKCS8 CLI tool
#define REPORT_ERROR report_error

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
    if (!bio) {
        return REPORT_ERROR(PKCS8_ERR_NULL_BIO_HANDLE);
    }
    
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
        return REPORT_ERROR(PKCS8_ERR_FILE_TOO_LARGE, params.max_size);
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
    if (!bio || !pkey) {
        return REPORT_ERROR(PKCS8_ERR_NULL_BIO_HANDLE);
    }
    
    ERR_clear_error();  // Clear any previous errors
    bool result = (format == "PEM") ?
        PEM_write_bio_PrivateKey(bio, pkey, nullptr, nullptr, 0, nullptr, nullptr) :
        i2d_PrivateKey_bio(bio, pkey);
    
    if (!result) {
        return REPORT_ERROR(PKCS8_ERR_FAILED_WRITE_KEY, format.c_str());
    }
    return true;
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
            return REPORT_ERROR(PKCS8_ERR_PASSWORD_TOO_LONG, DEFAULT_MAX_SENSITIVE_STRING_LENGTH);
        }
        
        *out_password = password;
        return true;
    }
    
    // Handle file:pathname format
    if (source.compare(0, 5, "file:") == 0) {
        std::string path = source.substr(5);
        bssl::UniquePtr<BIO> file_bio(BIO_new_file(path.c_str(), "r"));
        
        if (!file_bio) {
            return REPORT_ERROR(PKCS8_ERR_CANNOT_OPEN_PWFILE, path.c_str());
        }
        
        // Use fixed-size buffer with secure clearing
        char buf[DEFAULT_MAX_SENSITIVE_STRING_LENGTH];
        memset(buf, 0, sizeof(buf));
        
        int len = BIO_gets(file_bio.get(), buf, sizeof(buf));
        if (len <= 0) {
            OPENSSL_cleanse(buf, sizeof(buf));
            return REPORT_ERROR(PKCS8_ERR_CANNOT_READ_PWFILE);
        }
        
        // Remove trailing newline if present
        bool possible_truncation = (static_cast<size_t>(len) == DEFAULT_MAX_SENSITIVE_STRING_LENGTH - 1 && 
                                  buf[len - 1] != '\n' && buf[len - 1] != '\r');
        
        size_t buf_len = strlen(buf);
        while (buf_len > 0 && (buf[buf_len-1] == '\n' || buf[buf_len-1] == '\r')) {
            buf[--buf_len] = '\0';
        }
        
        // Keep warning as a direct fprintf since it's not an error
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
            return REPORT_ERROR(PKCS8_ERR_EMPTY_ENV_VAR);
        }
        
        const char* env_value = getenv(env_var.c_str());
        if (!env_value) {
            return REPORT_ERROR(PKCS8_ERR_ENV_VAR_NOT_SET,
                    env_var.c_str());
        }
        
        if (strlen(env_value) > DEFAULT_MAX_SENSITIVE_STRING_LENGTH) {
            return REPORT_ERROR(PKCS8_ERR_ENV_VAR_TOO_LONG,
                   env_var.c_str(), DEFAULT_MAX_SENSITIVE_STRING_LENGTH);
        }
        
        *out_password = env_value;
        return true;
    }
    
    // TODO: Implement EVP password prompting functionality similar to OpenSSL 1.1.1
    // This would handle cases where the password needs to be prompted from the user
    // interactively using EVP_read_pw_string or similar functionality.
    // See OpenSSL implementation in crypto/pem/pem_lib.c
    
    return REPORT_ERROR(PKCS8_ERR_UNSUPPORTED_PWFMT);
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

// Validates a key format string (PEM or DER)
static bool validate_key_format(const std::string& format, const char* option_name) {
  if (format != "PEM" && format != "DER") {
    return REPORT_ERROR(PKCS8_ERR_INVALID_FORMAT, option_name);
  }
  return true;
}

// SECURITY: Validates cipher algorithm against security allowlist
static bool validate_cipher(const std::string& cipher_name) {
    if (kSupportedCiphers.find(cipher_name) == kSupportedCiphers.end()) {
        REPORT_ERROR(PKCS8_ERR_UNSUPPORTED_CIPHER, cipher_name.c_str());
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
        REPORT_ERROR(PKCS8_ERR_UNKNOWN_PRF, prf_name.c_str());
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
                          PKCS8_ERROR_CODE code) {
    // SECURITY: Ensure passwords are securely cleared from memory
    secure_clear_string(passin);
    secure_clear_string(passout);
    return REPORT_ERROR(code);
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

// SECURITY: Helper function to read a private key in any format with validation
static bssl::UniquePtr<EVP_PKEY> read_private_key(BIO* in_bio, const char* passin, const std::string& format) {
  if (!in_bio) {
    REPORT_ERROR(PKCS8_ERR_NULL_BIO_HANDLE);
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
    REPORT_ERROR(PKCS8_ERR_FAILED_READ_KEY);
    return nullptr;
  }
  
  // For PEM format input (default)
  BIO_reset(in_bio);
  pkey.reset(PEM_read_bio_PrivateKey(in_bio, nullptr, nullptr, const_cast<char*>(passin)));
  if (pkey) {
    return pkey;
  }

  // If we get here, all attempts failed
  REPORT_ERROR(PKCS8_ERR_FAILED_READ_KEY);
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
  if (!validate_key_format(inform, "inform") || !validate_key_format(outform, "outform")) {
    return false;
  }

  if (in_path.empty()) {
    return REPORT_ERROR(PKCS8_ERR_MISSING_ARGUMENT);  
  }

  // Create input BIO with validation
  bssl::UniquePtr<BIO> in_bio(BIO_new_file(in_path.c_str(), "rb"));
  if (!in_bio) {
    return REPORT_ERROR(PKCS8_ERR_CANNOT_OPEN_FILE, in_path.c_str());
  }

  // Validate file size to prevent DoS attacks
  if (!validate_bio_size(in_bio.get())) {
    // validate_bio_size has already reported the specific error
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
    return REPORT_ERROR(PKCS8_ERR_CANNOT_OPEN_WRITE);
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
    return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_UNSUPPORTED_CIPHER);
  }

  if (!v2_prf.empty() && !validate_prf(v2_prf)) {
    return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_UNSUPPORTED_PRF);
  }

  // Read the private key using the improved method with format
  bssl::UniquePtr<EVP_PKEY> pkey = read_private_key(in_bio.get(), passin, inform);
  if (!pkey) {
    return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_FAILED_READ_KEY);
  }

  // Process the key based on user options
  if (!topk8) {
    // Case 1: Traditional format - simplest path
    bool result = write_key_bio(out_bio.get(), pkey.get(), outform);
    if (!result) {
      return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_FAILED_TRADITIONAL);
    }
    
    // Ensure data is flushed to disk
    BIO_flush(out_bio.get());
    
    // SECURITY: Clear passwords before returning
    secure_clear_string(passin_password);
    secure_clear_string(passout_password);
    return true;
  }
  
  // For all topk8 cases, we need to convert to PKCS8 format first
  bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(EVP_PKEY2PKCS8(pkey.get()));
  if (!p8inf) {
    return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_FAILED_CONVERT);
  }
  
  // Case 2: Unencrypted PKCS8 output
  if (nocrypt) {
    ERR_clear_error();
    bool result;
    
    if (outform == "PEM") {
      result = PEM_write_bio_PKCS8_PRIV_KEY_INFO(out_bio.get(), p8inf.get());
    } else { // DER
      result = i2d_PKCS8_PRIV_KEY_INFO_bio(out_bio.get(), p8inf.get());
    }
    
    if (!result) {
      return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_FAILED_WRITE_PKCS8);
    }
    
    BIO_flush(out_bio.get());
    secure_clear_string(passin_password);
    secure_clear_string(passout_password);
    return true;
  }
  
  // Case 3: Encrypted PKCS8 output
  
  // Passphrase is required for encryption
  if (!passout) {
    return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_MISSING_PASSOUT);
  }
  
  // Determine which cipher to use
  const EVP_CIPHER *cipher = nullptr;
  bool v2_specified = parsed_args.count("-v2") > 0;
  
  if (v2_specified) {
    if (v2_cipher.empty()) {
      return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_V2_NO_CIPHER);
    }
    
    // Already validated above
    cipher = EVP_get_cipherbyname(v2_cipher.c_str());
    if (!cipher) {
      // Should not happen if validation passed, but handle as a fallback
      return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_INIT_CIPHER_FAILED);
    }
  } else {
    // Default cipher if not specified
    cipher = EVP_aes_256_cbc();
  }
  
  // Handle PRF if specified
  if (!v2_prf.empty()) {
    int pbe_nid = OBJ_txt2nid(v2_prf.c_str());
    if (pbe_nid == NID_undef) {
      return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_UNKNOWN_PRF);
    }
    // This check is kept for compatibility with existing code
    if (pbe_nid != NID_hmacWithSHA1) {
      return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_INVALID_PRF);
    }
  }
  
  // Write the encrypted key in the appropriate format
  bool result;
  if (outform == "PEM") {
    result = PEM_write_bio_PKCS8PrivateKey(out_bio.get(), pkey.get(), 
                                         cipher, passout, strlen(passout),
                                         nullptr, nullptr);
  } else { // DER
    result = i2d_PKCS8PrivateKey_bio(out_bio.get(), pkey.get(),
                                    cipher, passout, strlen(passout),
                                    nullptr, nullptr);
  }
  
  if (!result) {
    return cleanup_and_fail(passin_password, passout_password, PKCS8_ERR_FAILED_WRITE_ENC);
  }

  // Ensure data is flushed to disk
  BIO_flush(out_bio.get());

  // SECURITY: Clear passwords before returning
  secure_clear_string(passin_password);
  secure_clear_string(passout_password);
  return true;
}
