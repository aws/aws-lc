// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <cerrno>
#include <climits>
#include <cstring>
#include <string>
#include "internal.h"

// Use PEM_BUFSIZE (defined in openssl/pem.h) for password buffer size to ensure
// compatibility with PEM functions and password callbacks throughout AWS-LC

// Detect the type of password source
static pass_util::Source DetectSource(const Password &source) {
  if (source.empty()) {
    return pass_util::Source::kNone;
  }
  if (source.get().compare(0, 5, "pass:") == 0) {
    return pass_util::Source::kPass;
  }
  if (source.get().compare(0, 5, "file:") == 0) {
    return pass_util::Source::kFile;
  }
  if (source.get().compare(0, 4, "env:") == 0) {
    return pass_util::Source::kEnv;
  }
  if (source.get().compare("stdin") == 0) {
    return pass_util::Source::kStdin;
  }
#ifndef _WIN32
  if (source.get().compare(0, 3, "fd:") == 0) {
    return pass_util::Source::kFd;
  }
#endif
  return pass_util::Source::kNone;
}

// Helper function to validate password sources and detect same-file case
static bool ValidateSource(Password &passin,
                           Password *passout = nullptr,
                           bool *same_file = nullptr) {
  // Always initialize same_file
  if (same_file) {
    *same_file = false;
  }

  // Validate passin format (if not empty)
  if (!passin.empty()) {
    pass_util::Source passin_type = DetectSource(passin);
    if (passin_type == pass_util::Source::kNone) {
      fprintf(stderr, "Invalid password format (use pass:, file:, env:, or stdin)\n");
      return false;
    }
  }

  // Validate passout format (if provided and not empty)
  if (passout && !passout->empty()) {
    pass_util::Source passout_type = DetectSource(*passout);
    if (passout_type == pass_util::Source::kNone) {
      fprintf(stderr, "Invalid password format (use pass:, file:, env:, or stdin)\n");
      return false;
    }

    // Detect same-file case if requested
    if (same_file && !passin.empty()) {
      pass_util::Source passin_type = DetectSource(passin);
      *same_file =
          (passin_type == pass_util::Source::kFile &&
           passout_type == pass_util::Source::kFile && passin.get() == passout->get()) ||
          (passin_type == pass_util::Source::kStdin &&
           passout_type == pass_util::Source::kStdin);
    }
  }

  return true;
}

static bool ExtractDirectPassword(Password &source) {
  // Check length before modification
  if (source.get().length() - 5 >= PEM_BUFSIZE) {
    fprintf(stderr, "Password exceeds maximum allowed length (%d bytes)\n",
            PEM_BUFSIZE - 1);
    return false;
  }

  // Remove "pass:" prefix by shifting the remaining content to the beginning
  source.get().erase(0, 5);
  return true;
}

static bool ExtractPasswordFromStream(Password &source,
                                      pass_util::Source source_type,
                                      bool skip_first_line = false,
                                      Password *passout = nullptr) {
  char buf[PEM_BUFSIZE] = {};
  bssl::UniquePtr<BIO> bio;
  
  // Initialize BIO based on source type
  if (source_type == pass_util::Source::kStdin) {
#ifdef _WIN32
    bio.reset(BIO_new_fp(stdin, BIO_NOCLOSE | BIO_FP_TEXT));
#else
    bio.reset(BIO_new_fp(stdin, BIO_NOCLOSE));
#endif
  } else if (source_type == pass_util::Source::kFile) {
    source.get().erase(0, 5); // Remove "file:" prefix
    bio.reset(BIO_new_file(source.get().c_str(), "r"));
#ifndef _WIN32
  } else if (source_type == pass_util::Source::kFd) {
    source.get().erase(0, 3);
    
    if (source.empty() || strspn(source.get().c_str(), "0123456789") != source.get().length()) {
      fprintf(stderr, "Invalid file descriptor\n");
      return false;
    }
    
    errno = 0;
    unsigned long fd_val = strtoul(source.get().c_str(), nullptr, 10);
    if (errno != 0 || fd_val > INT_MAX) {
      fprintf(stderr, "Invalid file descriptor\n");
      return false;
    }
    int fd = static_cast<int>(fd_val);
    bio.reset(BIO_new_fd(fd, BIO_NOCLOSE));
#endif
  } else {
    fprintf(stderr, "Unsupported source type for stream extraction\n");
    return false;
  }
  
  if (!bio) {
    if (source_type == pass_util::Source::kStdin) {
      fprintf(stderr, "Cannot open stdin\n");
#ifndef _WIN32
    } else if (source_type == pass_util::Source::kFd) {
      fprintf(stderr, "Cannot open file descriptor\n");
#endif
    } else {
      fprintf(stderr, "Cannot open password file\n");
    }
    return false;
  }

  auto read_password_line = [&](std::string& target) -> bool {
    int len = BIO_gets(bio.get(), buf, sizeof(buf));
    if (len <= 0) {
      OPENSSL_cleanse(buf, sizeof(buf));
      if (source_type == pass_util::Source::kStdin) {
        fprintf(stderr, "Failed to read password from stdin\n");
#ifndef _WIN32
      } else if (source_type == pass_util::Source::kFd) {
        fprintf(stderr, "Failed to read password from file descriptor\n");
#endif
      } else {
        fprintf(stderr, "Cannot read password file\n");
      }
      return false;
    }

    // Check for possible truncation
    if (static_cast<size_t>(len) == PEM_BUFSIZE - 1 && 
        buf[len - 1] != '\n' && buf[len - 1] != '\r') {
      OPENSSL_cleanse(buf, sizeof(buf));
      if (source_type == pass_util::Source::kStdin) {
        fprintf(stderr, "Password from stdin too long (maximum %d bytes)\n", PEM_BUFSIZE);
#ifndef _WIN32
      } else if (source_type == pass_util::Source::kFd) {
        fprintf(stderr, "Password from file descriptor too long (maximum %d bytes)\n", PEM_BUFSIZE);
#endif
      } else {
        fprintf(stderr, "Password file content too long (maximum %d bytes)\n", PEM_BUFSIZE);
      }
      return false;
    }

    // Trim trailing newlines
    while (len > 0 && (buf[len - 1] == '\n' || buf[len - 1] == '\r')) {
      len--;
    }
    
    target.assign(buf, len);
    OPENSSL_cleanse(buf, sizeof(buf));
    return true;
  };

  // Handle same-file case (read both passwords)
  if (passout) {
    if (!read_password_line(source.get()) || !read_password_line(passout->get())) {
      return false;
    }
  } else {
    // Handle skip_first_line if needed
    if (skip_first_line) {
      Password dummy;
      if (!read_password_line(dummy.get())) {
        return false;
      }
    }
    
    // Read single password
    if (!read_password_line(source.get())) {
      return false;
    }
  }

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
    fprintf(stderr, "Environment variable not set\n");
    return false;
  }

  size_t env_val_len = strlen(env_val);
  if (env_val_len == 0) {
    fprintf(stderr, "Environment variable is empty\n");
    return false;
  }
  if (env_val_len >= PEM_BUFSIZE) {
    fprintf(stderr, "Environment variable value too long (maximum %d bytes)\n",
            PEM_BUFSIZE - 1);
    return false;
  }

  // Replace source content with environment value
  source.get().assign(env_val, env_val_len);
  return true;
}

// Internal helper to extract password based on source type
static bool ExtractPasswordFromSource(Password &source,
                                      pass_util::Source type,
                                      bool skip_first_line = false,
                                      Password *passout = nullptr) {
  switch (type) {
    case pass_util::Source::kPass:
      return ExtractDirectPassword(source);
    case pass_util::Source::kFile:
      return ExtractPasswordFromStream(source, type, skip_first_line, passout);
    case pass_util::Source::kEnv:
      return ExtractPasswordFromEnv(source);
    case pass_util::Source::kStdin:
      return ExtractPasswordFromStream(source, type, skip_first_line, passout);
#ifndef _WIN32
    case pass_util::Source::kFd:
      return ExtractPasswordFromStream(source, type, skip_first_line, passout);
#endif
    default:
#ifndef _WIN32
      fprintf(stderr, "Invalid password format (use pass:, file:, env:, fd:, or stdin)\n");
#else
      fprintf(stderr, "Invalid password format (use pass:, file:, env:, or stdin)\n");
#endif
      return false;
  }
}

namespace pass_util {

bool ExtractPassword(Password &source) {
  if (!ValidateSource(source)) {
    return false;
  }

  if (source.empty()) {
    fprintf(stderr, "Invalid password format (use pass:, file:, env:, or stdin)\n");
    return false;
  }

  pass_util::Source type = DetectSource(source);
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
    pass_util::Source source_type = DetectSource(passin);
    return ExtractPasswordFromSource(passin, source_type, false, &passout);
  }

  // Extract passin (always from first line)
  if (!passin.empty()) {
    pass_util::Source passin_type = DetectSource(passin);
    if (!ExtractPasswordFromSource(passin, passin_type, false)) {
      return false;
    }
  }

  // Extract passout (from first line if different files, second line if same
  // file)
  if (!passout.empty()) {
    pass_util::Source passout_type = DetectSource(passout);
    if (!ExtractPasswordFromSource(passout, passout_type, same_file)) {
      return false;
    }
  }

  return true;
}

}  // namespace pass_util
