// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <cstring>
#include <string>
#include "internal.h"

// Maximum length limit for sensitive strings like passwords (4KB)
static constexpr size_t DEFAULT_MAX_SENSITIVE_STRING_LENGTH = 4096;

namespace password {

void SensitiveStringDeleter(std::string *str) {
  if (str && !str->empty()) {
    OPENSSL_cleanse(&(*str)[0], str->size());
  }
  delete str;
}

bool ExtractPassword(bssl::UniquePtr<std::string> &source) {
  // Empty source means empty password
  if (!source || source->empty()) {
    source.reset(new std::string());
    return true;
  }

  const std::string &source_str = *source;

  // Direct password: pass:password
  if (source_str.compare(0, 5, "pass:") == 0) {
    std::string password = source_str.substr(5);
    if (password.length() > DEFAULT_MAX_SENSITIVE_STRING_LENGTH) {
      fprintf(stderr, "Password exceeds maximum allowed length\n");
      return false;
    }
    source.reset(new std::string(std::move(password)));
    return true;
  }

  // Password from file: file:/path/to/file
  if (source_str.compare(0, 5, "file:") == 0) {
    std::string path = source_str.substr(5);
    bssl::UniquePtr<BIO> bio(BIO_new_file(path.c_str(), "r"));
    if (!bio) {
      fprintf(stderr, "Cannot open password file\n");
      return false;
    }
    char buf[DEFAULT_MAX_SENSITIVE_STRING_LENGTH] = {};
    int len = BIO_gets(bio.get(), buf, sizeof(buf));
    if (len <= 0) {
      OPENSSL_cleanse(buf, sizeof(buf));
      fprintf(stderr, "Cannot read password file\n");
      return false;
    }
    const bool possible_truncation =
        (static_cast<size_t>(len) == DEFAULT_MAX_SENSITIVE_STRING_LENGTH - 1 &&
         buf[len - 1] != '\n' && buf[len - 1] != '\r');
    if (possible_truncation) {
      OPENSSL_cleanse(buf, sizeof(buf));
      fprintf(stderr, "Password file content too long\n");
      return false;
    }
    size_t buf_len = len;
    while (buf_len > 0 &&
           (buf[buf_len - 1] == '\n' || buf[buf_len - 1] == '\r')) {
      buf[--buf_len] = '\0';
    }
    source.reset(new std::string(buf, buf_len));
    OPENSSL_cleanse(buf, sizeof(buf));
    return true;
  }

  // Password from environment variable: env:VAR_NAME
  if (source_str.compare(0, 4, "env:") == 0) {
    std::string env_var = source_str.substr(4);
    if (env_var.empty()) {
      fprintf(stderr, "Empty environment variable name\n");
      return false;
    }
    const char *env_val = getenv(env_var.c_str());
    if (!env_val) {
      fprintf(stderr, "Environment variable '%s' not set\n", env_var.c_str());
      return false;
    }
    size_t env_val_len = strlen(env_val);
    if (env_val_len == 0) {
      fprintf(stderr, "Environment variable '%s' is empty\n", env_var.c_str());
      return false;
    }
    if (env_val_len > DEFAULT_MAX_SENSITIVE_STRING_LENGTH) {
      fprintf(stderr, "Environment variable value too long\n");
      return false;
    }
    source.reset(new std::string(env_val));
    return true;
  }

  // Invalid format
  fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
  return false;
}

}  // namespace password
