// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <cstring>
#include <string>
#include "internal.h"

namespace pass_util {

// Detect the type of password source
static Source DetectSource(const Password &source) {
  if (source.empty()) {
    return Source::kNone;
  }
  if (source.get().compare(0, 5, "pass:") == 0) {
    return Source::kPass;
  }
  if (source.get().compare(0, 5, "file:") == 0) {
    return Source::kFile;
  }
  if (source.get().compare(0, 4, "env:") == 0) {
    return Source::kEnv;
  }
  if (source.get().compare("stdin") == 0) {
    return Source::kStdin;
  }
#ifndef _WIN32
  if (source.get().compare(0, 3, "fd:") == 0) {
    return Source::kFd;
  }
#endif
  return Source::kNone;
}

// Helper function to validate password sources and detect same-file case
static bool ValidateSource(Password &passin, Password *passout = nullptr,
                           bool *same_file = nullptr) {
  // Validate passin format (if not empty)
  if (!passin.empty()) {
    Source passin_type = DetectSource(passin);
    if (passin_type == Source::kNone) {
      fprintf(stderr,
              "Invalid password format (use pass:, file:, env:, or stdin)\n");
      return false;
    }
  }

  // Validate passout format (if provided and not empty)
  if (passout && !passout->empty()) {
    Source passout_type = DetectSource(*passout);
    if (passout_type == Source::kNone) {
      fprintf(stderr,
              "Invalid password format (use pass:, file:, env:, or stdin)\n");
      return false;
    }

    // Detect same-file case if requested
    if (same_file && !passin.empty()) {
      Source passin_type = DetectSource(passin);
      *same_file =
          (passin_type == Source::kFile && passout_type == Source::kFile &&
           passin.get() == passout->get()) ||
          (passin_type == Source::kStdin && passout_type == Source::kStdin);
    }
  }

  // Initialize same_file to false if not detected
  if (same_file && (!passout || passout->empty())) {
    *same_file = false;
  }

  return true;
}

static bool ExtractDirectPassword(Password &source) {
  // Check for additional colons in password portion after prefix
  if (source.get().find(':', 5) != std::string::npos) {
    fprintf(stderr,
            "Invalid password format (use pass:, file:, env:, or stdin)\n");
    return false;
  }

  // Check length before modification
  if (source.get().length() - 5 > PEM_BUFSIZE) {
    fprintf(stderr, "Password exceeds maximum allowed length (%d bytes)\n",
            PEM_BUFSIZE);
    return false;
  }

  // Remove "pass:" prefix by shifting the remaining content to the beginning
  source.get().erase(0, 5);
  return true;
}

static bool ExtractPasswordFromStream(Password &source, Source source_type,
                                      bool skip_first_line = false,
                                      Password *passout = nullptr) {
  char buf[PEM_BUFSIZE] = {};
  bssl::UniquePtr<BIO> bio;

  // Initialize BIO based on source type
  if (source_type == Source::kStdin) {
#ifdef OPENSSL_WINDOWS
    bio.reset(BIO_new_fp(stdin, BIO_NOCLOSE | BIO_FP_TEXT));
#else
    bio.reset(BIO_new_fp(stdin, BIO_NOCLOSE));
#endif
  } else if (source_type == Source::kFile) {
    source.get().erase(0, 5);  // Remove "file:" prefix
    bio.reset(BIO_new_file(source.get().c_str(), "r"));
#ifndef _WIN32
  } else if (source_type == Source::kFd) {
    source.get().erase(0, 3);

    if (source.empty() ||
        strspn(source.get().c_str(), "0123456789") != source.get().length()) {
      fprintf(stderr, "Invalid file descriptor: %s\n", source.get().c_str());
      return false;
    }

    int fd = atoi(source.get().c_str());
    if (fd < 0) {
      fprintf(stderr, "Invalid file descriptor: %s\n", source.get().c_str());
      return false;
    }
    bio.reset(BIO_new_fd(fd, BIO_NOCLOSE));
#endif
  } else {
    fprintf(stderr, "Unsupported source type for stream extraction\n");
    return false;
  }

  if (!bio) {
    if (source_type == Source::kStdin) {
      fprintf(stderr, "Cannot open stdin\n");
#if !defined(OPENSSL_WINDOWS)
    } else if (source_type == Source::kFd) {
      fprintf(stderr, "Cannot open file descriptor\n");
#endif
    } else {
      fprintf(stderr, "Cannot open password file\n");
    }
    return false;
  }

  auto read_password_line = [&](std::string &target) -> bool {
    int len = BIO_gets(bio.get(), buf, sizeof(buf));
    if (len <= 0) {
      OPENSSL_cleanse(buf, sizeof(buf));
      if (source_type == Source::kStdin) {
        fprintf(stderr, "Failed to read password from stdin\n");
#if !defined(OPENSSL_WINDOWS)
      } else if (source_type == Source::kFd) {
        fprintf(stderr, "Failed to read password from file descriptor\n");
#endif
      } else {
        fprintf(stderr, "Cannot read password file\n");
      }
      return false;
    }

    // Check for possible truncation
    if (static_cast<size_t>(len) == PEM_BUFSIZE - 1 && buf[len - 1] != '\n' &&
        buf[len - 1] != '\r') {
      OPENSSL_cleanse(buf, sizeof(buf));
      if (source_type == Source::kStdin) {
        fprintf(stderr, "Password from stdin too long (maximum %d bytes)\n",
                PEM_BUFSIZE);
#if !defined(OPENSSL_WINDOWS)
      } else if (source_type == Source::kFd) {
        fprintf(stderr,
                "Password from file descriptor too long (maximum %d bytes)\n",
                PEM_BUFSIZE);
#endif
      } else {
        fprintf(stderr, "Password file content too long (maximum %d bytes)\n",
                PEM_BUFSIZE);
      }
      return false;
    }

    // Trim trailing newlines
    while (len > 0 && (buf[len - 1] == '\n' || buf[len - 1] == '\r')) {
      len--;
    }

    target.assign(buf, len);
    return true;
  };

  // Handle same-file case (read both passwords)
  if (passout) {
    if (!read_password_line(source.get()) ||
        !read_password_line(passout->get())) {
      return false;
    }
  } else {
    // Handle skip_first_line if needed
    if (skip_first_line) {
      std::string dummy;
      if (!read_password_line(dummy)) {
        return false;
      }
    }

    // Read single password
    if (!read_password_line(source.get())) {
      return false;
    }
  }

  OPENSSL_cleanse(buf, sizeof(buf));
  return true;
}

static bool ExtractPasswordFromEnv(Password &source) {
  // Remove "env:" prefix
  source.get().erase(0, 4);

  if (source.empty()) {
    fprintf(stderr, "Empty environment variable name\n");
    return false;
  }

  const char *env_val = getenv(source.get().c_str());
  if (!env_val) {
    fprintf(stderr, "Environment variable '%s' not set\n",
            source.get().c_str());
    return false;
  }

  size_t env_val_len = strlen(env_val);
  if (env_val_len == 0) {
    fprintf(stderr, "Environment variable '%s' is empty\n",
            source.get().c_str());
    return false;
  }
  if (env_val_len > PEM_BUFSIZE) {
    fprintf(stderr, "Environment variable value too long (maximum %d bytes)\n",
            PEM_BUFSIZE);
    return false;
  }

  // Replace source content with environment value
  source.get() = std::string(env_val);
  return true;
}

// Internal helper to extract password based on source type
static bool ExtractPasswordFromSource(Password &source, Source type,
                                      bool skip_first_line = false,
                                      Password *passout = nullptr) {
  switch (type) {
    case Source::kPass:
      return ExtractDirectPassword(source);
    case Source::kFile:
      return ExtractPasswordFromStream(source, type, skip_first_line, passout);
    case Source::kEnv:
      return ExtractPasswordFromEnv(source);
    case Source::kStdin:
      return ExtractPasswordFromStream(source, type, skip_first_line, passout);
#if !defined(OPENSSL_WINDOWS)
    case Source::kFd:
      return ExtractPasswordFromStream(source, type, skip_first_line, passout);
#endif
    default:
#if !defined(OPENSSL_WINDOWS)
      fprintf(
          stderr,
          "Invalid password format (use pass:, file:, env:, fd:, or stdin)\n");
#else
      fprintf(stderr,
              "Invalid password format (use pass:, file:, env:, or stdin)\n");
#endif
      return false;
  }
}

bool ExtractPassword(Password &source) {
  if (!ValidateSource(source)) {
    return false;
  }

  if (source.empty()) {
    fprintf(stderr,
            "Invalid password format (use pass:, file:, env:, or stdin)\n");
    return false;
  }

  Source type = DetectSource(source);
  return ExtractPasswordFromSource(source, type);
}

bool ExtractPasswords(Password &passin, Password &passout) {
  // Use ValidateSource for all validation and same-file detection
  bool same_file = false;
  if (!ValidateSource(passin, &passout, &same_file)) {
    return false;
  }

  // Handle same_file case with single extraction call
  if (same_file && !passin.empty() && !passout.empty()) {
    Source source_type = DetectSource(passin);
    return ExtractPasswordFromSource(passin, source_type, same_file, &passout);
  }

  // Extract passin (always from first line)
  if (!passin.empty()) {
    Source passin_type = DetectSource(passin);
    if (!ExtractPasswordFromSource(passin, passin_type, false)) {
      return false;
    }
  }

  // Extract passout (from first line if different files, second line if same
  // file)
  if (!passout.empty()) {
    Source passout_type = DetectSource(passout);
    if (!ExtractPasswordFromSource(passout, passout_type, same_file)) {
      return false;
    }
  }

  return true;
}

}  // namespace pass_util
