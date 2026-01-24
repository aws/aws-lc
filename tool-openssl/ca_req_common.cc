// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "ca_req_common.h"

#include <cstdio>
#include <cstring>

#include <string>

#include <openssl/bio.h>
#include <openssl/conf.h>
#include <openssl/mem.h>
#include <openssl/pem.h>

#include "internal.h"

#define DEFAULT_CHAR_TYPE MBSTRING_ASC

const char *PromptField(const ReqField &field, char *buffer,
                        size_t buffer_size) {
  // Prompt with default value if available
  if (field.default_value && field.default_value[0]) {
    fprintf(stdout, "%s [%s]: ", field.short_desc, field.default_value);
  } else {
    fprintf(stdout, "%s: ", field.short_desc);
  }
  fflush(stdout);

  // Get input with fgets
  if (fgets(buffer, buffer_size, stdin) == NULL) {
    fprintf(stderr, "Error reading input\n");
    return NULL;
  }

  // Remove newline character and carriage return if present
  size_t len = OPENSSL_strnlen(buffer, buffer_size);
  if (len > 0 && buffer[len - 1] == '\n') {
    buffer[len - 1] = '\0';
    len--;
  }
#ifdef OPENSSL_WINDOWS
  if (len > 0 && buffer[len - 1] == '\r') {
    buffer[len - 1] = '\0';
    len--;
  }
#endif

  if (strcmp(buffer, ".") == 0) {
    // Empty entry requested
    return "";
  }
  if (len == 0 && field.default_value) {
    return field.default_value;
  }
  if (len > 0) {
    // Use provided input
    return buffer;
  }

  // Empty input and no default - use empty string
  return "";
}

bool LoadConfig(const std::string &config_path, bssl::UniquePtr<CONF> &conf) {
  bssl::UniquePtr<BIO> conf_bio(BIO_new_file(config_path.c_str(), "r"));
  if (!conf_bio) {
    fprintf(stderr, "Error: unable to load extension file from '%s'\n",
            config_path.c_str());
    return false;
  }

  conf.reset(NCONF_new(NULL));
  if (!conf) {
    fprintf(stderr, "Error: Failed to create extension config\n");
    return false;
  }

  if (NCONF_load_bio(conf.get(), conf_bio.get(), NULL) <= 0) {
    fprintf(stderr, "Error: Failed to load config from BIO\n");
    return false;
  }

  return true;
}

bool parse_bool(const char *str, bool default_value) {
  if (str == nullptr) {
    return default_value;
  }
  switch (*str) {
    case 'f':  // false
    case 'F':  // FALSE
    case 'n':  // no
    case 'N':  // NO
    case '0':  // 0
      return false;
    case 't':  // true
    case 'T':  // TRUE
    case 'y':  // yes
    case 'Y':  // YES
    case '1':  // 1
      return true;
    default:
      return default_value;
  }
}

bool LoadPrivateKey(const std::string &key_file_path,
                           Password &passin,
                           bssl::UniquePtr<EVP_PKEY> &pkey) {
  ScopedFILE key_file(fopen(key_file_path.c_str(), "rb"));

  if (!key_file) {
    fprintf(stderr, "Error: Failed to open %s", key_file_path.c_str());
    return false;
  }

  if (!passin.empty() && !pass_util::ExtractPassword(passin)) {
    fprintf(stderr, "Error: Failed to extract password\n");
    return false;
  }

  pkey.reset(PEM_read_PrivateKey(key_file.get(), nullptr, nullptr,
                                 const_cast<char *>(passin.get().c_str())));

  if (!pkey) {
    fprintf(stderr, "Error: Failed to read private key from %s\n",
            key_file_path.c_str());
    return false;
  }

  return true;
}

// Parse the subject string provided by a user with the -subj option.
bssl::UniquePtr<X509_NAME> ParseSubjectName(std::string &subject_string) {
  const char *subject_name_ptr = subject_string.c_str();

  if (*subject_name_ptr++ != '/') {
    fprintf(stderr,
            "name is expected to be in the format "
            "/type0=value0/type1=value1/type2=... where characters may "
            "be escaped by \\. This name is not in that format: '%s'\n",
            --subject_name_ptr);
    return nullptr;
  }

  // Create new X509_NAME
  bssl::UniquePtr<X509_NAME> name(X509_NAME_new());
  if (!name) {
    return nullptr;
  }

  std::string type;
  std::string value;

  while (*subject_name_ptr) {
    // Reset strings for new iteration
    type.clear();
    value.clear();

    // Parse type
    while (*subject_name_ptr && *subject_name_ptr != '=') {
      type += *subject_name_ptr++;
    }

    if (!*subject_name_ptr) {
      fprintf(stderr, "Hit end of string before finding the equals.\n");
      return nullptr;
    }

    // Skip '='
    subject_name_ptr++;

    // Parse value
    while (*subject_name_ptr && *subject_name_ptr != '/') {
      if (*subject_name_ptr == '\\' && *(subject_name_ptr + 1)) {
        // Handle escaped character
        subject_name_ptr++;
        value += *subject_name_ptr++;
      } else {
        value += *subject_name_ptr++;
      }
    }

    // Skip trailing '/' if present
    if (*subject_name_ptr == '/') {
      subject_name_ptr++;
    }

    // Convert type to NID, skip unknown attributes
    int nid = OBJ_txt2nid(type.c_str());
    if (nid == NID_undef) {
      fprintf(stderr, "Warning: Skipping unknown attribute \"%s\"\n",
              type.c_str());
      // Skip unknown attributes
      continue;
    }

    // Skip empty values
    if (value.empty()) {
      fprintf(stderr,
              "Warning: No value specified for attribute \"%s\", Skipped\n",
              type.c_str());
      continue;
    }

    // Add entry to the name
    if (!X509_NAME_add_entry_by_NID(name.get(), nid, DEFAULT_CHAR_TYPE,
                                    (unsigned char *)value.c_str(), -1, -1,
                                    0)) {
      OPENSSL_PUT_ERROR(X509, ERR_R_X509_LIB);
      return nullptr;
    }
  }

  return name;
}
