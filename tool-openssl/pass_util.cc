// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <cstring>
#include <string>
#include "internal.h"

// Use PEM_BUFSIZE (defined in openssl/pem.h) for password buffer size to ensure
// compatibility with PEM functions and password callbacks throughout AWS-LC

// Implementation details - not exposed in header
enum class PasswordSource { NONE, PASS, FILE, ENV };

// Detect the type of password source
static PasswordSource DetectSource(const bssl::UniquePtr<std::string> &source) {
  if (!source || source->empty()) {
    return PasswordSource::NONE;
  }
  if (source->compare(0, 5, "pass:") == 0) {
    return PasswordSource::PASS;
  }
  if (source->compare(0, 5, "file:") == 0) {
    return PasswordSource::FILE;
  }
  if (source->compare(0, 4, "env:") == 0) {
    return PasswordSource::ENV;
  }
  return PasswordSource::NONE;
}

// Extract password directly provided with pass: prefix
static bool ExtractDirectPassword(bssl::UniquePtr<std::string> &source) {
  // Check for additional colons in password portion after prefix
  if (source->find(':', 5) != std::string::npos) {
    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return false;
  }

  // Check length before modification
  if (source->length() - 5 > PEM_BUFSIZE) {
    fprintf(stderr, "Password exceeds maximum allowed length\n");
    return false;
  }

  // Remove "pass:" prefix by shifting the remaining content to the beginning
  source->erase(0, 5);
  return true;
}

// Extract password from file
static bool ExtractPasswordFromFile(bssl::UniquePtr<std::string> &source,
                                    bool skip_first_line = false) {
  // Remove "file:" prefix
  source->erase(0, 5);

  bssl::UniquePtr<BIO> bio(BIO_new_file(source->c_str(), "r"));
  if (!bio) {
    fprintf(stderr, "Cannot open password file\n");
    return false;
  }

  char buf[PEM_BUFSIZE] = {};

  // Skip first line if requested (for passout when using same file)
  if (skip_first_line) {
    if (BIO_gets(bio.get(), buf, sizeof(buf)) <= 0) {
      OPENSSL_cleanse(buf, sizeof(buf));
      fprintf(stderr, "Cannot read password file\n");
      return false;
    }
    OPENSSL_cleanse(buf, sizeof(buf));
  }

  // Read the password line
  int len = BIO_gets(bio.get(), buf, sizeof(buf));
  if (len <= 0) {
    OPENSSL_cleanse(buf, sizeof(buf));
    fprintf(stderr, "Cannot read password file\n");
    return false;
  }

  const bool possible_truncation =
      (static_cast<size_t>(len) == PEM_BUFSIZE - 1 && buf[len - 1] != '\n' &&
       buf[len - 1] != '\r');
  if (possible_truncation) {
    OPENSSL_cleanse(buf, sizeof(buf));
    fprintf(stderr, "Password file content too long\n");
    return false;
  }

  // Trim trailing newlines
  size_t buf_len = len;
  while (buf_len > 0 &&
         (buf[buf_len - 1] == '\n' || buf[buf_len - 1] == '\r')) {
    buf[--buf_len] = '\0';
  }

  // Replace source content with password
  *source = std::string(buf, buf_len);
  OPENSSL_cleanse(buf, sizeof(buf));
  return true;
}

// Extract password from environment variable
static bool ExtractPasswordFromEnv(bssl::UniquePtr<std::string> &source) {
  // Remove "env:" prefix
  source->erase(0, 4);

  if (source->empty()) {
    fprintf(stderr, "Empty environment variable name\n");
    return false;
  }

  const char *env_val = getenv(source->c_str());
  if (!env_val) {
    fprintf(stderr, "Environment variable '%s' not set\n", source->c_str());
    return false;
  }

  size_t env_val_len = strlen(env_val);
  if (env_val_len == 0) {
    fprintf(stderr, "Environment variable '%s' is empty\n", source->c_str());
    return false;
  }
  if (env_val_len > PEM_BUFSIZE) {
    fprintf(stderr, "Environment variable value too long\n");
    return false;
  }

  // Replace source content with environment value
  *source = std::string(env_val);
  return true;
}

// Internal helper to extract password based on source type
static bool ExtractPasswordFromSource(bssl::UniquePtr<std::string> &source,
                                      PasswordSource type,
                                      bool skip_first_line = false) {
  switch (type) {
    case PasswordSource::PASS:
      return ExtractDirectPassword(source);
    case PasswordSource::FILE:
      return ExtractPasswordFromFile(source, skip_first_line);
    case PasswordSource::ENV:
      return ExtractPasswordFromEnv(source);
    default:
      fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
      return false;
  }
}
namespace pass_util {

void SensitiveStringDeleter(std::string *str) {
  if (str && !str->empty()) {
    OPENSSL_cleanse(&(*str)[0], str->size());
  }
  delete str;
}

bool ExtractPassword(bssl::UniquePtr<std::string> &source) {
  // Empty source pointer is invalid
  if (!source) {
    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return false;
  }

  // Empty string without prefix is invalid
  if (source->empty()) {
    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return false;
  }

  // Use DetectSource to identify the password source type
  PasswordSource type = DetectSource(source);
  if (type == PasswordSource::NONE) {
    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return false;
  }

  // Use the helper function to extract the password
  return ExtractPasswordFromSource(source, type);
}

bool ExtractPasswords(bssl::UniquePtr<std::string> &passin,
                      bssl::UniquePtr<std::string> &passout) {
  // Validate input parameters
  if (!passin || !passout) {
    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return false;
  }

  // Detect password sources BEFORE any modification
  PasswordSource passin_type = DetectSource(passin);
  PasswordSource passout_type = DetectSource(passout);
  
  // Check for same file case using original values
  bool same_file = (passin_type == PasswordSource::FILE &&
                    passout_type == PasswordSource::FILE &&
                    *passin == *passout);

  // Handle invalid source formats
  if ((!passin->empty() && passin_type == PasswordSource::NONE) ||
      (!passout->empty() && passout_type == PasswordSource::NONE)) {
    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return false;
  }

  // Extract passin (always from first line)
  if (!passin->empty()) {
    if (!ExtractPasswordFromSource(passin, passin_type, false)) {
      return false;
    }
  }

  // Extract passout (from first line if different files, second line if same file)
  if (!passout->empty()) {
    if (!ExtractPasswordFromSource(passout, passout_type, same_file)) {
      return false;
    }
  }

  return true;
}

}  // namespace pass_util
