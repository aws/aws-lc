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

// Detect the type of password source
static pass_util::Source DetectSource(const bssl::UniquePtr<std::string> &source) {
  if (!source || source->empty()) {
    return pass_util::Source::kNone;
  }
  if (source->compare(0, 5, "pass:") == 0) {
    return pass_util::Source::kPass;
  }
  if (source->compare(0, 5, "file:") == 0) {
    return pass_util::Source::kFile;
  }
  if (source->compare(0, 4, "env:") == 0) {
    return pass_util::Source::kEnv;
  }
  return pass_util::Source::kNone;
}

// Helper function to validate password sources and detect same-file case
static bool ValidateSource(bssl::UniquePtr<std::string> &passin,
                          bssl::UniquePtr<std::string> *passout = nullptr,
                          bool *same_file = nullptr) {
  // Validate passin
  if (!passin) {
    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return false;
  }
  
  // Validate passout if provided
  if (passout && !*passout) {
    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return false;
  }
  
  // Validate passin format (if not empty)
  if (!passin->empty()) {
    pass_util::Source passin_type = DetectSource(passin);
    if (passin_type == pass_util::Source::kNone) {
      fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
      return false;
    }
  }
  
  // Validate passout format (if provided and not empty)
  if (passout && *passout && !(*passout)->empty()) {
    pass_util::Source passout_type = DetectSource(*passout);
    if (passout_type == pass_util::Source::kNone) {
      fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
      return false;
    }
    
    // Detect same-file case if requested
    if (same_file && !passin->empty()) {
      pass_util::Source passin_type = DetectSource(passin);
      *same_file = (passin_type == pass_util::Source::kFile &&
                    passout_type == pass_util::Source::kFile &&
                    *passin == **passout);
    }
  }
  
  // Initialize same_file to false if not detected
  if (same_file && (!passout || !*passout)) {
    *same_file = false;
  }
  
  return true;
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
    fprintf(stderr, "Password exceeds maximum allowed length (%d bytes)\n", PEM_BUFSIZE);
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
      (static_cast<size_t>(len) == PEM_BUFSIZE - 1) && buf[len - 1] != '\n' &&
       buf[len - 1] != '\r';
  if (possible_truncation) {
    OPENSSL_cleanse(buf, sizeof(buf));
    fprintf(stderr, "Password file content too long (maximum %d bytes)\n", PEM_BUFSIZE);
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
    fprintf(stderr, "Environment variable value too long (maximum %d bytes)\n", PEM_BUFSIZE);
    return false;
  }

  // Replace source content with environment value
  *source = std::string(env_val);
  return true;
}

// Internal helper to extract password based on source type
static bool ExtractPasswordFromSource(bssl::UniquePtr<std::string> &source,
                                    pass_util::Source type,
                                    bool skip_first_line = false) {
  switch (type) {
    case pass_util::Source::kPass:
      return ExtractDirectPassword(source);
    case pass_util::Source::kFile:
      return ExtractPasswordFromFile(source, skip_first_line);
    case pass_util::Source::kEnv:
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
  // Use ValidateSource for all validation
  if (!ValidateSource(source)) {
    return false;
  }

  // Handle empty source (invalid for single password)
  if (source->empty()) {
    fprintf(stderr, "Invalid password format (use pass:, file:, or env:)\n");
    return false;
  }

  // Extract the password
  pass_util::Source type = DetectSource(source);
  return ExtractPasswordFromSource(source, type);
}

bool ExtractPasswords(bssl::UniquePtr<std::string> &passin,
                      bssl::UniquePtr<std::string> &passout) {
  // Use ValidateSource for all validation and same-file detection
  bool same_file = false;
  if (!ValidateSource(passin, &passout, &same_file)) {
    return false;
  }

  // Extract passin (always from first line)
  if (!passin->empty()) {
    pass_util::Source passin_type = DetectSource(passin);
    if (!ExtractPasswordFromSource(passin, passin_type, false)) {
      return false;
    }
  }

  // Extract passout (from first line if different files, second line if same file)
  if (!passout->empty()) {
    pass_util::Source passout_type = DetectSource(passout);
    if (!ExtractPasswordFromSource(passout, passout_type, same_file)) {
      return false;
    }
  }

  return true;
}

}  // namespace pass_util
