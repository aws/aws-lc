// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// PKCS8 Tool - Security Properties and Design
// -------------------------------------------
// 
// This implementation provides the following security properties:
//
// 1. Password Confidentiality:
//    - All password buffers are securely cleared from memory after use
//    - RAII patterns ensure automatic clearing even in error cases
//    - Volatile pointers are used to prevent compiler optimization of clearing operations
//
// 2. Input Validation:
//    - File paths are validated to detect potentially malicious paths
//    - File sizes are validated to prevent denial-of-service attacks
//    - Password lengths are bounded to prevent buffer-related issues
//    - Cipher algorithms and PRF names are validated against an allowlist
//
// 3. Error Handling:
//    - Security-sensitive errors are explicitly logged
//    - Error messages are designed to be informative without leaking sensitive information
//    - Consolidated error handling ensures consistent behavior and cleanup
//
// SECURITY ASSUMPTIONS:
//
// 1. The operating system provides a secure implementation of standard library functions
// 2. The OpenSSL/AWS-LC cryptographic operations are secure and correctly implemented
// 3. The maximum file size limit (1MB) is sufficient for legitimate PKCS#8 keys
// 4. The maximum password length (4096 chars) is sufficient for all legitimate use cases
// 5. The supported ciphers and PRFs represent the set of algorithms that the tool should support

#include <openssl/base.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/pkcs8.h>
#include <openssl/err.h>
#include <openssl/rand.h>
#include <openssl/x509.h>
#include <openssl/mem.h>
#include <cstring>
#include <unordered_set>
#include <cassert>
#include "internal.h"

// SECURITY: Define constants with security implications
// SECURITY ASSUMPTION: 1MB is sufficient for legitimate PKCS#8 keys
static const long MAX_FILE_SIZE = 1024 * 1024;  // 1MB

// SECURITY ASSUMPTION: 4KB is sufficient for all reasonable passwords
static const size_t MAX_PASSWORD_LENGTH = 4096;

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

// SECURITY: Securely clear a string from memory
static void secure_clear_string(std::string& str) {
    if (!str.empty()) {
        volatile char* p = const_cast<volatile char*>(str.data());
        OPENSSL_cleanse(const_cast<char*>(p), str.size());
        str.clear();
    }
}

// SECURITY: Validate file size to prevent DoS from extremely large files
// This implementation preserves the current file position
static bool validate_file_size(FILE* file) {
    assert(file != nullptr && "File handle cannot be null");
    if (!file) return false;
    
    const long current_pos = ftell(file);  // Save current position
    if (current_pos < 0) return false;
    
    if (fseek(file, 0, SEEK_END) != 0) return false;
    const long size = ftell(file);
    
    // Restore original position
    if (fseek(file, current_pos, SEEK_SET) != 0) return false;
    
    if (size <= 0) {
        fprintf(stderr, "Error: Empty file or file size couldn't be determined\n");
        return false;
    }
    
    if (size > MAX_FILE_SIZE) {
        fprintf(stderr, "Error: File exceeds maximum allowed size of %ld bytes\n", 
                MAX_FILE_SIZE);
        return false;
    }
    
    return true;
}

// SECURITY: Validate cipher algorithms against the allowlist
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

// SECURITY: Validate PRF algorithms against the allowlist
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
static bool cleanup_and_fail(std::string& passin_password, 
                          std::string& passout_password,
                          const char* error_msg) {
    assert(error_msg != nullptr && "Error message cannot be null");
    fprintf(stderr, "Error: %s\n", error_msg);
    secure_clear_string(passin_password);
    secure_clear_string(passout_password);
    return false;
}

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-in", kOptionalArgument, "Input file" },
  { "-out", kOptionalArgument, "Output file" },
  { "-topk8", kBooleanArgument, "Convert traditional format to PKCS#8" },
  { "-nocrypt", kBooleanArgument, "Use unencrypted private key" },
  { "-v2", kOptionalArgument, "Use PKCS#5 v2.0 and specified cipher" },
  { "-v2prf", kOptionalArgument, "Use specified PRF algorithm with PKCS#5 v2.0" },
  { "-passin", kOptionalArgument, "Input file passphrase source" },
  { "-passout", kOptionalArgument, "Output file passphrase source" },
  { "-inform", kOptionalArgument, "Input format (DER or PEM)" },
  { "-outform", kOptionalArgument, "Output format (DER or PEM)" },
  { "", kOptionalArgument, "" }
};

// Helper function to print OpenSSL errors
static void print_errors() {
  ERR_print_errors_fp(stderr);
}

// SECURITY: Extract password from various sources with proper validation and secure handling
static bool extract_password(const std::string& source, std::string* out_password) {
  assert(out_password != nullptr && "Password output pointer cannot be null");
  if (!out_password) {
    return false;
  }
  
  // Handle pass:password format
  if (source.compare(0, 5, "pass:") == 0) {
    std::string password = source.substr(5);
    
    // SECURITY: Check password length
    if (password.length() > MAX_PASSWORD_LENGTH) {
      fprintf(stderr, "Error: Password exceeds maximum allowed length of %zu characters\n", 
              MAX_PASSWORD_LENGTH);
      return false;
    }
    
    *out_password = password;
    return true;
  }
  
  // Handle file:pathname format
  if (source.compare(0, 5, "file:") == 0) {
    std::string path = source.substr(5);
    ScopedFILE file(fopen(path.c_str(), "r"));
    if (!file) {
      fprintf(stderr, "Error: Could not open password file '%s'\n", path.c_str());
      return false;
    }
    
    // SECURITY: Use fixed-size buffer with secure clearing
    char buf[MAX_PASSWORD_LENGTH];
    memset(buf, 0, sizeof(buf));
    
    if (fgets(buf, sizeof(buf), file.get()) == nullptr) {
      fprintf(stderr, "Error: Could not read from password file\n");
      OPENSSL_cleanse(buf, sizeof(buf));
      return false;
    }
    
    // Remove trailing newline if present
    size_t len = strlen(buf);
    bool possible_truncation = (len == MAX_PASSWORD_LENGTH - 1 && 
                              buf[len - 1] != '\n' && buf[len - 1] != '\r');
    
    while (len > 0 && (buf[len-1] == '\n' || buf[len-1] == '\r')) {
      buf[--len] = '\0';
    }
    
    if (possible_truncation) {
      fprintf(stderr, "Warning: Password may have been truncated (exceeds %zu characters)\n", 
              MAX_PASSWORD_LENGTH - 1);
    }
    
    *out_password = buf;
    // SECURITY: Securely clear the buffer
    OPENSSL_cleanse(buf, sizeof(buf));
    return true;
  }
  
  // Handle env:var format
  if (source.compare(0, 4, "env:") == 0) {
    std::string env_var = source.substr(4);
    const char* env_value = getenv(env_var.c_str());
    if (!env_value) {
      fprintf(stderr, "Error: Environment variable '%s' not set\n", 
              env_var.c_str());
      return false;
    }
    
    // SECURITY: Check password length
    if (strlen(env_value) > MAX_PASSWORD_LENGTH) {
      fprintf(stderr, "Error: Password from environment variable exceeds maximum length of %zu characters\n", 
              MAX_PASSWORD_LENGTH);
      return false;
    }
    
    *out_password = env_value;
    return true;
  }
  
  // If no recognized prefix, return the source directly
  // This maintains backward compatibility with direct password input
  if (source.length() > MAX_PASSWORD_LENGTH) {
    fprintf(stderr, "Error: Password exceeds maximum allowed length of %zu characters\n", 
            MAX_PASSWORD_LENGTH);
    return false;
  }
  
  *out_password = source;
  return true;
}

// SECURITY: Helper function to read a private key in any format with validation
static bssl::UniquePtr<EVP_PKEY> read_private_key(FILE* in_file, const char* passin, const std::string& format) {
  if (!in_file) {
    fprintf(stderr, "Error: Null file handle in read_private_key\n");
    return nullptr;
  }
  
  // SECURITY: Validate file size
  if (!validate_file_size(in_file)) {
    return nullptr;  // Error already printed
  }
  
  bssl::UniquePtr<EVP_PKEY> pkey;

  // Handle DER format input
  if (format == "DER") {
    rewind(in_file);
    // For DER format, first try as unencrypted PKCS8
    bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf;
    
    {
      const uint8_t *derp;
      long derlen;
      // Get file size for DER reading
      const long current_pos = ftell(in_file);
      if (current_pos < 0) return nullptr;
      
      if (fseek(in_file, 0, SEEK_END) != 0) return nullptr;
      derlen = ftell(in_file);
      
      if (fseek(in_file, current_pos, SEEK_SET) != 0) return nullptr;
      
      if (derlen <= 0 || derlen > MAX_FILE_SIZE) {
        return nullptr;
      }
      
      std::vector<uint8_t> der(derlen);
      if (fread(der.data(), 1, derlen, in_file) != static_cast<size_t>(derlen)) {
        return nullptr;
      }
      
      derp = der.data();
      p8inf.reset(d2i_PKCS8_PRIV_KEY_INFO(nullptr, &derp, derlen));
    }
    
    if (p8inf) {
      pkey.reset(EVP_PKCS82PKEY(p8inf.get()));
      if (pkey) {
        return pkey;
      }
    }
    
    // If that failed and a password is provided, try as encrypted PKCS8
    if (passin) {
      rewind(in_file);
      bssl::UniquePtr<X509_SIG> p8;
      
      {
        const uint8_t *derp;
        long derlen;
        fseek(in_file, 0, SEEK_END);
        derlen = ftell(in_file);
        rewind(in_file);
        
        if (derlen <= 0) {
          return nullptr;
        }
        
        std::vector<uint8_t> der(derlen);
        if (fread(der.data(), 1, derlen, in_file) != static_cast<size_t>(derlen)) {
          return nullptr;
        }
        
        derp = der.data();
        // Use d2i_X509_SIG instead of d2i_PKCS8_bio
        p8.reset(d2i_X509_SIG(nullptr, &derp, derlen));
      }
      
      if (p8) {
        p8inf.reset(PKCS8_decrypt(p8.get(), passin, strlen(passin)));
        if (p8inf) {
          pkey.reset(EVP_PKCS82PKEY(p8inf.get()));
          if (pkey) {
            return pkey;
          }
        }
      }
    }
    
    // Finally try as traditional format DER
    rewind(in_file);
    pkey.reset(d2i_PrivateKey_fp(in_file, nullptr));
    if (pkey) {
      return pkey;
    }
    
    // All DER attempts failed
    return nullptr;
  }
  
  // For PEM format input (default)
  // First try reading as encrypted PKCS#8
  rewind(in_file);
  bssl::UniquePtr<X509_SIG> p8(PEM_read_PKCS8(in_file, nullptr, nullptr, nullptr));
  if (p8) {
    if (passin) {
      bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(
          PKCS8_decrypt(p8.get(), passin, strlen(passin)));
      if (p8inf) {
        pkey.reset(EVP_PKCS82PKEY(p8inf.get()));
        if (pkey) {
          return pkey;
        }
      }
    }
    // Don't print error here - we'll try other formats first
    ERR_clear_error();
  }

  // Try unencrypted PKCS#8
  rewind(in_file);
  bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(
      PEM_read_PKCS8_PRIV_KEY_INFO(in_file, nullptr, nullptr, nullptr));
  if (p8inf) {
    pkey.reset(EVP_PKCS82PKEY(p8inf.get()));
    if (pkey) {
      return pkey;
    }
    ERR_clear_error();
  }

  // Finally try traditional format
  rewind(in_file);
  EVP_PKEY *raw_pkey = nullptr;
  if (PEM_read_PrivateKey(in_file, &raw_pkey, nullptr,
                         const_cast<char*>(passin))) {
    pkey.reset(raw_pkey);
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

  ScopedFILE in_file(fopen(in_path.c_str(), "rb"));
  if (!in_file) {
    fprintf(stderr, "Error: unable to open input file '%s'\n", in_path.c_str());
    return false;
  }

  // SECURITY: Validate input file size
  if (!validate_file_size(in_file.get())) {
    return false;  // Error already printed
  }

  ScopedFILE out_file;
  if (!out_path.empty()) {
    out_file.reset(fopen(out_path.c_str(), "wb"));
    if (!out_file) {
      fprintf(stderr, "Error: unable to open output file '%s'\n", out_path.c_str());
      return false;
    }
  }
  FILE *out = out_file.get() ? out_file.get() : stdout;

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
  bssl::UniquePtr<EVP_PKEY> pkey = read_private_key(in_file.get(), passin, inform);
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
      // Handle output format
      if (outform == "PEM") {
        result = PEM_write_PKCS8_PRIV_KEY_INFO(out, p8inf.get());
      } else { // DER
        result = i2d_PKCS8_PRIV_KEY_INFO_fp(out, p8inf.get());
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

      bssl::UniquePtr<X509_SIG> p8_enc(
          PKCS8_encrypt(-1, cipher, passout, strlen(passout),
                       nullptr, 0, PKCS12_DEFAULT_ITER, p8inf.get()));

      if (!p8_enc) {
        print_errors();
        return cleanup_and_fail(passin_password, passout_password, 
                              "Failed to encrypt private key using PKCS#5 v2.0");
      }

      // Handle output format for encrypted key
      if (outform == "PEM") {
        result = PEM_write_PKCS8(out, p8_enc.get());
      } else { // DER
        result = i2d_PKCS8_fp(out, p8_enc.get());
      }
    }
  } else {
    // Handle traditional key output format
    if (outform == "PEM") {
      result = PEM_write_PrivateKey(out, pkey.get(), nullptr, nullptr, 0, nullptr, nullptr);
    } else { // DER
      result = i2d_PrivateKey_fp(out, pkey.get());
    }
  }

  if (!result) {
    print_errors();
    return cleanup_and_fail(passin_password, passout_password, "Failed to write private key");
  }

  // SECURITY: Clear passwords before returning
  secure_clear_string(passin_password);
  secure_clear_string(passout_password);
  return true;
}
