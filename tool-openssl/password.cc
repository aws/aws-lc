// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/evp.h>
#include <openssl/err.h>
#include <string>
#include <cstring>
#include "internal.h"

// Maximum length limit for sensitive strings like passwords (4KB)
static constexpr size_t DEFAULT_MAX_SENSITIVE_STRING_LENGTH = 4096;

namespace password {

void SensitiveStringDeleter(std::string* str) {
    if (str && !str->empty()) {
        OPENSSL_cleanse(&(*str)[0], str->size());
    }
    delete str;
}

bool HandlePassOptions(bssl::UniquePtr<std::string> *passin_arg,
                      bssl::UniquePtr<std::string> *passout_arg) {
  // Handle passin if provided
  if (passin_arg && *passin_arg) {
    bssl::UniquePtr<std::string> extracted_passin = ExtractPassword(*passin_arg);
    if (!extracted_passin) {
      return false;
    }
    *passin_arg = std::move(extracted_passin);
  }
  
  // Handle passout if provided
  if (passout_arg && *passout_arg) {
    // Check if both arguments point to the same source and passin was already processed
    bool same_source = (passin_arg && *passin_arg && passout_arg && *passout_arg && 
                       **passin_arg == **passout_arg);
    
    if (same_source) {
      // Create a new string to avoid sharing the same memory
      bssl::UniquePtr<std::string> extracted_passout(
          new std::string(**passin_arg));
      *passout_arg = std::move(extracted_passout);
    } else {
      // Extract output password separately
      bssl::UniquePtr<std::string> extracted_passout = ExtractPassword(*passout_arg);
      if (!extracted_passout) {
        return false;
      }
      *passout_arg = std::move(extracted_passout);
    }
  }
  
  return true;
}

bssl::UniquePtr<std::string> ExtractPassword(const bssl::UniquePtr<std::string>& source) {
    // Create a new string and wrap it in a UniquePtr
    std::string* str = new std::string();
    bssl::UniquePtr<std::string> result(str);
    
    // Empty source means empty password
    if (!source || source->empty()) {
        return result;
    }

    const std::string& source_str = *source;

    // Direct password: pass:password
    if (source_str.compare(0, 5, "pass:") == 0) {
        std::string password = source_str.substr(5); 
        if (password.length() > DEFAULT_MAX_SENSITIVE_STRING_LENGTH) {
            fprintf(stderr, "Password exceeds maximum allowed length\n");
            return bssl::UniquePtr<std::string>();
        }
        *str = std::move(password);
        return result;
    }

    // Password from file: file:/path/to/file
    if (source_str.compare(0, 5, "file:") == 0) {
        std::string path = source_str.substr(5);
        bssl::UniquePtr<BIO> bio(BIO_new_file(path.c_str(), "r"));
        if (!bio) {
            fprintf(stderr, "Cannot open password file\n");
            return bssl::UniquePtr<std::string>();
        }
        char buf[DEFAULT_MAX_SENSITIVE_STRING_LENGTH] = {};
        int len = BIO_gets(bio.get(), buf, sizeof(buf));
        if (len <= 0) {
            OPENSSL_cleanse(buf, sizeof(buf));
            fprintf(stderr, "Cannot read password file\n");
            return bssl::UniquePtr<std::string>();
        }
        const bool possible_truncation = (static_cast<size_t>(len) == DEFAULT_MAX_SENSITIVE_STRING_LENGTH - 1 && 
                                        buf[len - 1] != '\n' && buf[len - 1] != '\r');
        if (possible_truncation) {
            OPENSSL_cleanse(buf, sizeof(buf));
            fprintf(stderr, "Password file content too long\n");
            return bssl::UniquePtr<std::string>();
        }
        size_t buf_len = len;
        while (buf_len > 0 && (buf[buf_len-1] == '\n' || buf[buf_len-1] == '\r')) {
            buf[--buf_len] = '\0';
        }
        *str = std::string(buf);
        OPENSSL_cleanse(buf, sizeof(buf));
        return result;
    }

    // Password from environment variable: env:VAR_NAME
    if (source_str.compare(0, 4, "env:") == 0) {
        std::string env_var = source_str.substr(4);
        if (env_var.empty()) {
            fprintf(stderr, "Empty environment variable name\n");
            return bssl::UniquePtr<std::string>();
        }
        const char* env_val = getenv(env_var.c_str());
        if (!env_val) {
            fprintf(stderr, "Environment variable '%s' not set\n", env_var.c_str());
            return bssl::UniquePtr<std::string>();
        }
        size_t env_val_len = strlen(env_val);
        if (env_val_len == 0) {
            fprintf(stderr, "Environment variable '%s' is empty\n", env_var.c_str());
            return bssl::UniquePtr<std::string>();
        }
        if (env_val_len > DEFAULT_MAX_SENSITIVE_STRING_LENGTH) {
            fprintf(stderr, "Environment variable value too long\n");
            return bssl::UniquePtr<std::string>();
        }
        *str = std::string(env_val);
        return result;
    }

    // Invalid format
    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return bssl::UniquePtr<std::string>();
}

} // namespace password
